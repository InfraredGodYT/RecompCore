// RecompCore: StaticRecomp CPU core - SMC and chunk validation.
// SPDX-License-Identifier: GPL-2.0-or-later

#include "Core/PowerPC/StaticRecomp/StaticRecompCore.h"
#include "Core/System.h"
#include "Core/PowerPC/MMU.h"
#include "Core/PowerPC/JitInterface.h"
#include "Common/Logging/Log.h"
#include <algorithm>
#include <cstdio>
#include <cstring>

namespace
{
u32 ReadGuestBE32(const u8* bytes)
{
  return (static_cast<u32>(bytes[0]) << 24) | (static_cast<u32>(bytes[1]) << 16) |
         (static_cast<u32>(bytes[2]) << 8) | bytes[3];
}

// The SDK keeps every linked REL on __OSModuleList (OSModuleQueue at
// 0x800030C8: head, tail). Each OSModuleInfo starts with id, link.next,
// link.prev, numSections, sectionInfoOffset, ..., version (+0x1C).
constexpr u32 OS_MODULE_LIST_HEAD = 0x800030C8u;
constexpr u32 OS_MODULE_LIST_MAX = 64;  // guard against a corrupt (cyclic) list
constexpr u32 REL_HEADER_SIZE = 0x40;

bool GuestRangeInRam(u32 address, u32 length, u32 ram_size)
{
  if (address < 0x80000000u)
    return false;
  const u64 offset = static_cast<u64>(address - 0x80000000u);
  return offset + length <= ram_size;
}

// OSLink rewrites header and section-table offsets into absolute addresses.
// Accept both forms so a module seen mid-link resolves the same way.
u32 RelOffsetToAddress(u32 value, u32 header_address, u32 file_size, u32 ram_size)
{
  if (value < file_size)
    return header_address + value;
  if (value < ram_size)
    return value | 0x80000000u;
  return value;
}
}

void StaticRecompCore::ReadOSModuleList(std::vector<u32>* headers) const
{
  headers->clear();
  if (!m_guest.ram || !GuestRangeInRam(OS_MODULE_LIST_HEAD, 8, m_guest.ram_size))
    return;
  u32 node = ReadGuestBE32(m_guest.ram + (OS_MODULE_LIST_HEAD - 0x80000000u));
  while (node != 0)
  {
    if ((node & 3u) != 0 || !GuestRangeInRam(node, REL_HEADER_SIZE, m_guest.ram_size) ||
        headers->size() >= OS_MODULE_LIST_MAX)
    {
      headers->clear();  // not a list we can trust: map nothing
      return;
    }
    headers->push_back(node);
    node = ReadGuestBE32(m_guest.ram + (node - 0x80000000u) + 4);
  }
}

void StaticRecompCore::RefreshRelSectionsIfModuleListChanged()
{
  if (!m_has_rel_modules || !m_guest.ram)
    return;

  // Signature: every linked module's header address, id and section table.
  // The table is included because OSLink enqueues a module before it finishes
  // rewriting the section offsets (BSS gets its address last); the mapping
  // must follow those writes too.
  ReadOSModuleList(&m_rel_list_headers);
  m_rel_list_scratch.clear();
  for (const u32 header_address : m_rel_list_headers)
  {
    const u8* header = m_guest.ram + (header_address - 0x80000000u);
    const u32 id = ReadGuestBE32(header);
    const u32 num_sections = ReadGuestBE32(header + 0x0c);
    const u32 info = ReadGuestBE32(header + 0x10);
    u64 table_hash = 0xCBF29CE484222325ull;
    const u32 info_address = info >= 0x80000000u ? info : header_address + info;
    if (num_sections <= 4096 &&
        GuestRangeInRam(info_address, num_sections * 8, m_guest.ram_size))
    {
      // Word-at-a-time mix: this runs every slice, and any change to an
      // entry must change the signature, nothing more.
      const u8* table = m_guest.ram + (info_address - 0x80000000u);
      for (u32 i = 0; i < num_sections * 2; ++i)
      {
        u32 word;
        std::memcpy(&word, table + i * 4, sizeof(word));
        table_hash = (table_hash ^ word) * 0x100000001B3ull;
      }
    }
    m_rel_list_scratch.push_back((static_cast<u64>(header_address) << 32) | id);
    m_rel_list_scratch.push_back(table_hash);
  }
  if (m_rel_list_scratch == m_rel_list_signature)
    return;
  m_rel_list_signature = m_rel_list_scratch;
  RefreshRelSections();
}

void StaticRecompCore::RefreshRelSections()
{
  if (!m_module || m_module->num_rel_modules == 0 || !m_guest.ram || m_guest.ram_size < 0x40)
    return;

  std::vector<ActiveRelSection> discovered;
  std::vector<u32> bases(m_module->num_rel_slots, 0);
  std::vector<u32> headers;
  ReadOSModuleList(&headers);
  for (const u32 header_address : headers)
  {
    const u8* header = m_guest.ram + (header_address - 0x80000000u);
    const u32 id = ReadGuestBE32(header);
    const u32 num_sections = ReadGuestBE32(header + 0x0c);
    const u32 version = ReadGuestBE32(header + 0x1c);

    // Which compiled module is this? Match id, version and section count,
    // then every compiled code section's size (ids alone are not unique:
    // a game may ship several modules under one id).
    const StaticRecompRelModule* match = nullptr;
    u32 info_address = 0;
    u32 matches = 0;
    for (u32 module_index = 0; module_index < m_module->num_rel_modules; ++module_index)
    {
      const StaticRecompRelModule& module = m_module->rel_modules[module_index];
      if (module.module_id != id || module.version != version ||
          module.section_count != num_sections)
        continue;
      const u32 candidate_info = RelOffsetToAddress(ReadGuestBE32(header + 0x10), header_address,
                                                    module.file_size, m_guest.ram_size);
      if (candidate_info != header_address + module.section_info_offset ||
          !GuestRangeInRam(candidate_info, num_sections * 8, m_guest.ram_size))
        continue;
      bool sizes_match = true;
      for (u32 s = 0; s < module.num_sections && sizes_match; ++s)
      {
        const StaticRecompRelSection& section = module.sections[s];
        const u8* entry = m_guest.ram + (candidate_info - 0x80000000u) + section.section_index * 8;
        sizes_match = ReadGuestBE32(entry + 4) == section.size;
      }
      if (!sizes_match)
        continue;
      match = &module;
      info_address = candidate_info;
      ++matches;
    }
    if (matches != 1)
    {
      if (m_rel_unmatched_logged.insert(header_address).second)
      {
        std::fprintf(stderr,
                     "[staticrecomp] REL id=%u at 0x%08X: %s; its code stays on the "
                     "fallback core\n",
                     id, header_address,
                     matches == 0 ? "not in this module" : "ambiguous match");
      }
      continue;
    }

    // Runtime address of every section. A section with a size but no address
    // yet (BSS before OSLink assigns it) means the module is still being
    // linked: map nothing for it until the signature changes again.
    std::vector<u32> module_bases(num_sections, 0);
    bool ready = true;
    for (u32 s = 0; s < num_sections && ready; ++s)
    {
      const u8* entry = m_guest.ram + (info_address - 0x80000000u) + s * 8;
      const u32 raw = ReadGuestBE32(entry) & ~1u;
      const u32 size = ReadGuestBE32(entry + 4);
      if (size == 0)
        continue;
      if (raw == 0)
      {
        ready = false;
        break;
      }
      const u32 runtime =
          RelOffsetToAddress(raw, header_address, match->file_size, m_guest.ram_size);
      if (!GuestRangeInRam(runtime, size, m_guest.ram_size))
      {
        ready = false;
        break;
      }
      module_bases[s] = runtime;
    }
    if (!ready)
      continue;

    for (u32 s = 0; s < num_sections; ++s)
      bases[match->first_slot + s] = module_bases[s];
    for (u32 s = 0; s < match->num_sections; ++s)
    {
      const StaticRecompRelSection& section = match->sections[s];
      discovered.push_back({match->module_id, section.section_index, section.linked_start,
                            module_bases[section.section_index], section.size});
    }
  }

  // Native REL code reads these; publish them before any of it can run.
  std::copy(bases.begin(), bases.end(), m_module->rel_slot_bases);

  const bool changed = discovered.size() != m_active_rel_sections.size() ||
                       !std::equal(discovered.begin(), discovered.end(),
                                   m_active_rel_sections.begin(),
                                   [](const ActiveRelSection& left, const ActiveRelSection& right) {
                                     return left.module_id == right.module_id &&
                                            left.section_index == right.section_index &&
                                            left.linked_start == right.linked_start &&
                                            left.runtime_start == right.runtime_start &&
                                            left.size == right.size;
                                   });
  if (!changed)
    return;
  m_active_rel_sections = std::move(discovered);
  ++m_rel_mapping_generation;
  for (u32 i = 0; i < m_chunk_rel_sections.size(); ++i)
  {
    if (m_chunk_rel_sections[i] < 0)
      continue;
    if (m_chunk_state[i] == CHUNK_FAILED && m_failed_chunks != 0)
      --m_failed_chunks;
    m_chunk_state[i] = CHUNK_UNVERIFIED;
    m_effective_chunk_hashes[i] = m_module->chunk_hashes[i];
  }
}

bool StaticRecompCore::ResolveNativeAddress(u32 runtime_address, u32* linked_address,
                                            u32* rel_section_index)
{
  // Fast path for DOL code, the common case: a RAM address whose lookup
  // entry is a non-REL chunk. REL code is mapped from heap memory, which
  // never overlaps the DOL's text, so such a hit cannot be REL code.
  if (runtime_address >= 0x80000000u && runtime_address - 0x80000000u < m_lookup_ram_size)
  {
    const int chunk = m_chunk_lookup_table[(runtime_address - 0x80000000u) >> 2];
    if (chunk >= 0 && m_chunk_rel_sections[chunk] < 0)
    {
      *linked_address = runtime_address;
      if (rel_section_index)
        *rel_section_index = 0xffffffffu;
      return true;
    }
  }

  const auto resolve_active = [&]() {
    for (u32 i = 0; i < m_active_rel_sections.size(); ++i)
    {
      const ActiveRelSection& section = m_active_rel_sections[i];
      if (runtime_address >= section.runtime_start &&
          static_cast<u64>(runtime_address) < static_cast<u64>(section.runtime_start) + section.size)
      {
        *linked_address = section.linked_start + (runtime_address - section.runtime_start);
        if (rel_section_index)
          *rel_section_index = i;
        return true;
      }
    }
    return false;
  };
  if (resolve_active())
    return true;
  const int direct_index = GetAddressLookupIndex(runtime_address);
  if (direct_index >= 0 && direct_index < static_cast<int>(m_chunk_lookup_table.size()))
  {
    const int chunk = m_chunk_lookup_table[direct_index];
    if (chunk >= 0 && m_chunk_rel_sections[chunk] < 0)
    {
      *linked_address = runtime_address;
      if (rel_section_index)
        *rel_section_index = 0xffffffffu;
      return true;
    }
  }
  // Not DOL code and not inside a linked REL. The mapping is refreshed from
  // the OS module list once per slice, not here: misses are frequent (heap
  // code, exception vectors) and must stay cheap.
  return false;
}

bool StaticRecompCore::ResolveRuntimeAddress(u32 linked_address, u32* runtime_address) const
{
  // Only addresses inside the virtual REL window can be linked REL code.
  if (m_rel_window_size != 0 &&
      (linked_address < m_rel_window_start || linked_address - m_rel_window_start >= m_rel_window_size))
  {
    *runtime_address = linked_address;
    return true;
  }
  for (const ActiveRelSection& section : m_active_rel_sections)
  {
    if (linked_address >= section.linked_start &&
        static_cast<u64>(linked_address) < static_cast<u64>(section.linked_start) + section.size)
    {
      *runtime_address = section.runtime_start + (linked_address - section.linked_start);
      return true;
    }
  }
  *runtime_address = linked_address;
  return true;
}

u32 StaticRecompCore::TranslateRelAddress(u32 linked_address)
{
  u32 runtime_address = linked_address;
  ResolveRuntimeAddress(linked_address, &runtime_address);
  return runtime_address;
}

int StaticRecompCore::GetAddressLookupIndex(u32 address) const
{
  if (address >= 0x80000000u && address < 0x80000000u + m_lookup_ram_size)
    return static_cast<int>((address - 0x80000000u) >> 2);
  if (address >= 0x90000000u && address < 0x90000000u + m_lookup_exram_size)
    return static_cast<int>((m_lookup_ram_size >> 2) + ((address - 0x90000000u) >> 2));
  if (m_rel_window_size != 0 && address >= m_rel_window_start &&
      address - m_rel_window_start < m_rel_window_size)
  {
    return static_cast<int>((m_lookup_ram_size >> 2) + (m_lookup_exram_size >> 2) +
                            ((address - m_rel_window_start) >> 2));
  }
  return -1;
}

void StaticRecompCore::InitLookupTable(u32 ram_size, u32 exram_size)
{
  if (m_lookup_ram_size == ram_size && m_lookup_exram_size == exram_size)
    return;

  m_lookup_ram_size = ram_size;
  m_lookup_exram_size = exram_size;
  m_rel_window_start = 0;
  m_rel_window_size = 0;

  if (!m_module)
  {
    m_chunk_lookup_table.clear();
    return;
  }

  // REL code compiled at virtual addresses outside RAM/EXRAM gets its own
  // window of lookup entries.
  if (m_module->num_rel_modules != 0)
  {
    u32 low = 0xFFFFFFFFu;
    u64 high = 0;
    for (u32 m = 0; m < m_module->num_rel_modules; ++m)
    {
      const StaticRecompRelModule& module = m_module->rel_modules[m];
      for (u32 s = 0; s < module.num_sections; ++s)
      {
        low = std::min(low, module.sections[s].linked_start);
        high = std::max<u64>(high, static_cast<u64>(module.sections[s].linked_start) +
                                       module.sections[s].size);
      }
    }
    const bool in_ram = low >= 0x80000000u && low - 0x80000000u < ram_size;
    const bool in_exram = exram_size != 0 && low >= 0x90000000u && low - 0x90000000u < exram_size;
    if (!in_ram && !in_exram && high > low)
    {
      m_rel_window_start = low;
      m_rel_window_size = static_cast<u32>(high - low);
    }
  }

  u32 total_instructions = (ram_size + exram_size + m_rel_window_size) >> 2;
  m_chunk_lookup_table.assign(total_instructions, -1);

  for (u32 i = 0; i < m_module->num_chunk_ranges; ++i)
  {
    const auto& chunk = m_module->chunk_ranges[i];
    int start_idx = GetAddressLookupIndex(chunk.start);
    // Look up the last instruction, not chunk.end: a chunk ending exactly at
    // the end of a region would otherwise get no entries at all.
    const int last_idx = chunk.end > chunk.start ? GetAddressLookupIndex(chunk.end - 4u) : -1;
    int end_idx = last_idx >= 0 ? last_idx + 1 : -1;

    if (start_idx >= 0 && end_idx >= start_idx)
    {
      for (int idx = start_idx; idx < end_idx; ++idx)
      {
        m_chunk_lookup_table[idx] = static_cast<int>(i);
      }
    }
  }
}

int StaticRecompCore::ChunkIndexOf(u32 address)
{
  if (!m_module_active || m_chunk_lookup_table.empty())
    return -1;

  u32 linked_address = address;
  if (!ResolveNativeAddress(address, &linked_address, nullptr))
    return -1;
  int idx = GetAddressLookupIndex(linked_address);
  if (idx < 0 || idx >= static_cast<int>(m_chunk_lookup_table.size()))
    return -1;

  return m_chunk_lookup_table[idx];
}

bool StaticRecompCore::FastDispatchableAt(u32 address)
{
  if (IsForcedFallbackAddress(address))
    return false;
  const int index = ChunkIndexOf(address);
  return index >= 0 && m_chunk_state[index] == CHUNK_VERIFIED;
}

bool StaticRecompCore::DispatchableAt(u32 address)
{
  if (IsForcedFallbackAddress(address))
    return false;
  const int index = ChunkIndexOf(address);
  if (index < 0)
    return false;
  if (m_chunk_state[index] == CHUNK_UNVERIFIED)
    VerifyChunk(static_cast<u32>(index));
  return m_chunk_state[index] == CHUNK_VERIFIED;
}

bool StaticRecompCore::IsForcedFallbackAddress(u32 address) const
{
  for (const StaticRecompRange& range : m_forced_fallback_ranges)
  {
    if (address >= range.start && address < range.end)
      return true;
  }
  return false;
}

bool StaticRecompCore::ChunkContainsHostCall(u32 index) const
{
  if (!m_module_source.host_call_contains || index >= m_chunk_host_call_state.size())
    return false;

  u8& state = m_chunk_host_call_state[index];
  if (state != 0)
    return state == 2;

  const auto& chunk = m_module->chunk_ranges[index];
  bool found = false;
  if (m_module_source.host_call_range_contains)
  {
    found = m_module_source.host_call_range_contains(
        chunk.start, chunk.end, m_module_source.host_call_user);
  }
  else
  {
    for (u32 address = chunk.start; address < chunk.end; address += 4)
    {
      if (IsHostCallAddress(address))
      {
        found = true;
        break;
      }
    }
  }
  state = found ? 2 : 1;
  if (found)
    std::fprintf(stderr, "[staticrecomp] mod fallback: chunk [0x%08X,0x%08X)\n", chunk.start,
                 chunk.end);
  return found;
}

void StaticRecompCore::VerifyChunk(u32 index)
{
  const auto& chunk = m_module->chunk_ranges[index];
  auto& memory = m_system.GetMemory();
  const u32 ram_size = memory.GetRamSizeReal();
  u32 runtime_start = chunk.start;
  ResolveRuntimeAddress(chunk.start, &runtime_start);
  const u32 offset = runtime_start - 0x80000000u;
  const u32 length = chunk.end - chunk.start;
  ++m_verifications;

  if (runtime_start < 0x80000000u || offset >= ram_size || length > ram_size - offset)
  {
    m_chunk_state[index] = CHUNK_FAILED;
    ++m_failed_chunks;
    ERROR_LOG_FMT(POWERPC, "StaticRecomp: chunk [0x{:08X},0x{:08X}) outside guest RAM",
                  chunk.start, chunk.end);
    return;
  }

  // FNV-1a 64, matching gen_module_tables.py.
  const u8* bytes = memory.GetRAM() + offset;
  u64 hash = 0xCBF29CE484222325ull;
  for (u32 i = 0; i < length; ++i)
  {
    hash ^= bytes[i];
    hash *= 0x100000001B3ull;
  }

  if (m_effective_chunk_hashes[index] == 0)
    m_effective_chunk_hashes[index] = hash;

  if (hash == m_effective_chunk_hashes[index])
  {
    m_chunk_state[index] = CHUNK_VERIFIED;
  }
  else
  {
    m_chunk_state[index] = CHUNK_FAILED;
    ++m_failed_chunks;
    std::fprintf(stderr,
                 "[staticrecomp] SMC: chunk [0x%08X,0x%08X) hash mismatch; interpreter until "
                 "next invalidation (%u failed)\n",
                 chunk.start, chunk.end, m_failed_chunks);
    WARN_LOG_FMT(POWERPC,
                 "StaticRecomp: chunk [0x{:08X},0x{:08X}) failed verification (guest code "
                 "differs from module); interpreter until next invalidation",
                 chunk.start, chunk.end);
  }
}

bool StaticRecompCore::IsIdleLoopAt(u32 address)
{
  const auto cached = m_idle_loop_cache.find(address);
  if (cached != m_idle_loop_cache.end())
    return cached->second;

  // Dolphin's own analysis, so a loop idles here exactly when Jit64 would
  // idle it (OpType::Integer/Load only, no stores, branches only to itself,
  // no CTR use, no reading a register before the loop overwrites it).
  PPCAnalyst::BlockStats stats{};
  PPCAnalyst::BlockRegStats gpa{};
  PPCAnalyst::BlockRegStats fpa{};
  PPCAnalyst::CodeBlock block;
  block.m_stats = &stats;
  block.m_gpa = &gpa;
  block.m_fpa = &fpa;
  constexpr std::size_t MAX_LOOP_INSTRUCTIONS = 32;
  if (m_code_buffer.size() < MAX_LOOP_INSTRUCTIONS)
    m_code_buffer.resize(MAX_LOOP_INSTRUCTIONS);
  analyzer.Analyze(address, &block, &m_code_buffer, MAX_LOOP_INSTRUCTIONS);

  bool idle = false;
  for (u32 i = 0; i < block.m_num_instructions; ++i)
  {
    if (m_code_buffer[i].branchIsIdleLoop && m_code_buffer[i].branchTo == address)
    {
      idle = true;
      break;
    }
  }
  m_idle_loop_cache.emplace(address, idle);
  return idle;
}

void StaticRecompCore::OnICacheInvalidate(u32 address, u32 length)
{
  // Forward to the fallback JIT only if the range holds code it compiled,
  // tested with its valid-block bitset one 32-byte line at a time -- exactly
  // the filter Jit64's dcbx loop applies before it invalidates. Without it,
  // every flushed range of plain data (video frames, vertex buffers) makes
  // the block cache erase three hash sets for every 4 bytes of the range.
  if (m_fallback_jit && length != 0)
  {
    JitBaseBlockCache* const fallback_cache = m_fallback_jit->GetBlockCache();
    const u32* const valid_bits = fallback_cache->GetBlockBitSet();
    auto& mmu = m_system.GetMMU();
    bool has_code = false;
    u32 line = address & ~0x1fu;
    const u64 end = static_cast<u64>(address) + length;
    u32 page = 0xFFFFFFFFu;
    u32 page_physical = 0;
    bool page_valid = false;
    for (; static_cast<u64>(line) < end && !has_code; line += 32)
    {
      if ((line & ~0xFFFu) != page)
      {
        page = line & ~0xFFFu;
        const auto translated = mmu.JitCache_TranslateAddress(page);
        page_valid = translated.valid;
        page_physical = translated.address;
      }
      if (!page_valid)
        continue;
      const u32 bit = (page_physical + (line - page)) >> 5;
      has_code = (valid_bits[bit >> 5] & (1u << (bit & 31u))) != 0;
      if (line > 0xFFFFFFE0u)
        break;
    }
    if (has_code)
      fallback_cache->InvalidateICache(address, length, false);
  }

  // Code that changed may no longer be (or may now be) a busy-wait loop.
  if (!m_idle_loop_cache.empty() && length != 0)
  {
    const u64 end = static_cast<u64>(address) + length;
    auto it = m_idle_loop_cache.lower_bound(address);
    while (it != m_idle_loop_cache.end() && it->first < end)
      it = m_idle_loop_cache.erase(it);
  }

  if (!m_module_active || length == 0)
    return;
  u32 linked_address = address;
  ResolveNativeAddress(address, &linked_address, nullptr);
  address = linked_address;
  const u32 last = address + (length - 1u);

  // Binary search to find the first chunk index that could possibly overlap (chunk.end > address)
  u32 lo = 0;
  u32 hi = m_module->num_chunk_ranges;
  while (lo < hi)
  {
    const u32 mid = lo + (hi - lo) / 2;
    if (m_module->chunk_ranges[mid].end <= address)
      lo = mid + 1;
    else
      hi = mid;
  }

  for (u32 i = lo; i < m_module->num_chunk_ranges; ++i)
  {
    const auto& chunk = m_module->chunk_ranges[i];
    if (chunk.start > last)
      break;

    if (m_chunk_state[i] != CHUNK_UNVERIFIED)
    {
      if (m_chunk_state[i] == CHUNK_FAILED)
        --m_failed_chunks;
      m_chunk_state[i] = CHUNK_UNVERIFIED;
      ++m_reverify_events;
    }
  }
}
