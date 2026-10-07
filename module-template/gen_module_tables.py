#!/usr/bin/env python3
"""Generate module_tables.inc for a dolphin-chassis static recompilation module.

Parses the generated dispatcher's coverage ranges out of generated.h. Both
the original per-chunk address guards and DolRecomp's compact offset-table
dispatch runs are supported. SMC candidate ranges come from generated_smc.txt,
so the module ABI tables can never drift from a DolRecomp regen.
"""
import re
import sys
from pathlib import Path


FNV64_OFFSET = 0xCBF29CE484222325
FNV64_PRIME = 0x100000001B3
MASK64 = (1 << 64) - 1


def fnv1a64(data: bytes) -> int:
    h = FNV64_OFFSET
    for b in data:
        h = ((h ^ b) * FNV64_PRIME) & MASK64
    return h


def load_dol_text(dol_path: Path):
    """Return a function mapping a guest address range to the DOL's bytes."""
    dol = dol_path.read_bytes()

    def be32(off: int) -> int:
        return int.from_bytes(dol[off : off + 4], "big")

    sections = []
    for i in range(18):  # 7 text + 11 data sections share the layout
        file_off = be32(0x00 + i * 4)
        address = be32(0x48 + i * 4)
        size = be32(0x90 + i * 4)
        if file_off and address and size:
            sections.append((address, size, file_off))

    def read_range(start: int, end: int) -> bytes:
        for address, size, file_off in sections:
            if address <= start and end <= address + size:
                lo = file_off + (start - address)
                return dol[lo : lo + (end - start)]
        raise ValueError(f"range [0x{start:08X},0x{end:08X}) not inside one DOL section")

    return read_range


def load_rel_metadata(path: Path):
    """Parse DolRecomp's generated_rels.txt (written by --rels).

    Returns (slot_count, modules) where each module is a dict with id,
    version, sections, section_info, file_size, first_slot, name and a list
    of (index, linked_start, size, exec, bss) sections.
    """
    if not path.is_file():
        return 0, []
    slots = 0
    modules = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        kind, _, rest = line.partition(" ")
        if kind == "slots":
            slots = int(rest)
            continue
        fields = dict(f.split("=", 1) for f in rest.split() if "=" in f)
        if kind == "module":
            modules.append({
                "name": rest.split()[0],
                "id": int(fields["id"]),
                "version": int(fields["version"]),
                "sections": int(fields["sections"]),
                "section_info": int(fields["section_info"], 16),
                "file_size": int(fields["file_size"], 16),
                "first_slot": int(fields["first_slot"]),
                "section_list": [],
            })
        elif kind == "section":
            modules[-1]["section_list"].append((
                int(rest.split()[0]),
                int(fields["addr"], 16),
                int(fields["size"], 16),
                fields["exec"] == "1",
                fields["bss"] == "1",
            ))
    return slots, modules


def write_rel_tables(f, slots: int, modules) -> None:
    """REL tables for the chassis (module ABI v4)."""
    exec_sections = [
        (m, s) for m in modules for s in m["section_list"] if s[3]
    ]
    if not modules:
        f.write("#define MODULE_REL_MODULES NULL\n")
        f.write("#define MODULE_REL_MODULE_COUNT 0u\n")
        f.write("#define MODULE_REL_SLOT_BASES NULL\n")
        f.write("#define MODULE_REL_SLOT_COUNT 0u\n")
        return
    f.write("static const StaticRecompRelSection s_rel_sections[] = {\n")
    for m, (index, addr, size, _exec, _bss) in exec_sections:
        f.write(f"    {{{m['id']}u, {index}u, 0x{addr:08X}u, 0x{size:X}u}}, /* {m['name']} */\n")
    f.write("};\n")
    f.write("static const StaticRecompRelModule s_rel_modules[] = {\n")
    cursor = 0
    for m in modules:
        count = sum(1 for s in m["section_list"] if s[3])
        f.write(
            f"    {{{m['id']}u, {m['version']}u, {m['sections']}u, 0x{m['section_info']:X}u, "
            f"0x{m['file_size']:X}u, &s_rel_sections[{cursor}], {count}u, "
            f"{m['first_slot']}u}}, /* {m['name']} */\n"
        )
        cursor += count
    f.write("};\n")
    # Written by the chassis, read by REL code (extern in generated.h).
    f.write(f"u32 dolrecomp_rel_base[{slots}];\n")
    f.write("#define MODULE_REL_MODULES s_rel_modules\n")
    f.write(f"#define MODULE_REL_MODULE_COUNT {len(modules)}u\n")
    f.write("#define MODULE_REL_SLOT_BASES dolrecomp_rel_base\n")
    f.write(f"#define MODULE_REL_SLOT_COUNT {slots}u\n")


def main() -> int:
    generated_h = Path(sys.argv[1])
    smc_txt = Path(sys.argv[2])
    dol_path = Path(sys.argv[3])
    out_path = Path(sys.argv[4])
    rel_slots, rel_modules = load_rel_metadata(generated_h.with_name("generated_rels.txt"))
    rel_code = [
        (addr, addr + size)
        for m in rel_modules
        for (_i, addr, size, is_exec, _b) in m["section_list"]
        if is_exec
    ]

    header = generated_h.read_text()
    code_ranges = {
        (int(a, 16), int(b, 16))
        for a, b in re.findall(
            r"address >= (0x[0-9A-Fa-f]+)u && address < (0x[0-9A-Fa-f]+)u", header
        )
    }
    for base, span in re.findall(
        r"u32\s+offset\s*=\s*address\s*-\s*(0x[0-9A-Fa-f]+)u\s*;\s*"
        r"if\s*\(\s*offset\s*<\s*(0x[0-9A-Fa-f]+)u",
        header,
    ):
        start = int(base, 16)
        code_ranges.add((start, start + int(span, 16)))
    if not code_ranges:
        print("error: no coverage ranges found in", generated_h, file=sys.stderr)
        return 1
    code_ranges = sorted(code_ranges)

    # Chunk table: one range per generated func_XXXXXXXX translation unit.
    # A chunk is the demotion granule for the chassis SMC guard: an icache
    # invalidation inside a chunk retires exactly that chunk to the
    # interpreter for the session.
    func_addrs = sorted(
        int(a, 16)
        for a in re.findall(r"void func_([0-9A-Fa-f]{8})\(CPUState\* ctx\);", header)
    )
    if not func_addrs:
        print("error: no func_ declarations found in", generated_h, file=sys.stderr)
        return 1
    chunk_ranges = []
    for i, addr in enumerate(func_addrs):
        containing = next(((a, b) for a, b in code_ranges if a <= addr < b), None)
        if containing is None:
            print(f"error: func_{addr:08X} outside all code ranges", file=sys.stderr)
            return 1
        end = containing[1]
        if i + 1 < len(func_addrs) and containing[0] <= func_addrs[i + 1] < containing[1]:
            end = func_addrs[i + 1]
        chunk_ranges.append((addr, end))

    smc_ranges = []
    for line in smc_txt.read_text().splitlines():
        m = re.match(r"(0x[0-9A-Fa-f]+)-(0x[0-9A-Fa-f]+)", line.strip())
        if m:
            # File ranges are inclusive instruction addresses; ABI ranges are
            # end-exclusive byte ranges.
            smc_ranges.append((int(m.group(1), 16), int(m.group(2), 16) + 4))
    smc_ranges.sort()

    with out_path.open("w") as f:
        f.write("// Generated by gen_module_tables.py — do not edit.\n")
        f.write("static const StaticRecompRange s_code_ranges[] = {\n")
        for a, b in code_ranges:
            f.write(f"    {{0x{a:08X}u, 0x{b:08X}u}},\n")
        f.write("};\n")
        f.write(f"#define MODULE_CODE_RANGE_COUNT {len(code_ranges)}u\n")
        f.write("static const StaticRecompRange s_smc_ranges[] = {\n")
        if smc_ranges:
            for a, b in smc_ranges:
                f.write(f"    {{0x{a:08X}u, 0x{b:08X}u}},\n")
        else:
            f.write("    {0u, 0u}, /* C and MSVC do not support zero-sized arrays. */\n")
        f.write("};\n")
        f.write(f"#define MODULE_SMC_RANGE_COUNT {len(smc_ranges)}u\n")
        f.write("static const StaticRecompRange s_chunk_ranges[] = {\n")
        for a, b in chunk_ranges:
            f.write(f"    {{0x{a:08X}u, 0x{b:08X}u}},\n")
        f.write("};\n")
        f.write(f"#define MODULE_CHUNK_RANGE_COUNT {len(chunk_ranges)}u\n")
        # FNV-1a 64 of each chunk's original text, so the chassis can verify
        # that guest RAM still holds the code this module was compiled from.
        # REL chunks get 0 ("adopt on first verify"): their bytes in RAM carry
        # relocations for wherever the game loaded the module, so no hash can
        # be known ahead of time. The chassis only maps a REL once the OS has
        # linked it and its header and section sizes match.
        read_range = load_dol_text(dol_path)
        f.write("static const u64 s_chunk_hashes[] = {\n")
        for a, b in chunk_ranges:
            if any(lo <= a and b <= hi for lo, hi in rel_code):
                f.write("    0x0000000000000000u, /* REL */\n")
            else:
                f.write(f"    0x{fnv1a64(read_range(a, b)):016X}u,\n")
        f.write("};\n")
        write_rel_tables(f, rel_slots, rel_modules)
    print(
        f"module_tables.inc: {len(code_ranges)} code ranges, "
        f"{len(smc_ranges)} smc ranges, {len(chunk_ranges)} chunk ranges (hashed), "
        f"{len(rel_modules)} REL modules, {rel_slots} REL slots"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
