# Scope and evidence for the ELF boot linker unit manual

## Purpose and audience

This manual describes low-level linker unit scenarios for compiler and linker
maintainers. It checks layout, symbol resolution, relocation bytes, TLS storage,
fail-closed behavior and script placement; it does not boot the generated image.
The detailed scenarios remain folded below.

## Preconditions and primary workflow

Use the checked-in ELF fixtures under `test/fixtures/linker/elf` and a supported
compiler runtime. Select the layout plan whose ENTRY exists in the object's
symbol table, link the fixture image, then inspect section sizes and patched
bytes against the executable assertions. In the CODE_4/CODE_6 GOTTPOFF scenario,
`code_gottpoff_x64.o` defines `_start`; the plan therefore selects `_start`.
Both relocations must share one eight-byte GOT slot, with the expected PC-relative
displacements and a TLS TPOFF value of -8. The fixture recipe records the Mold
2.42 oracle; the broader spec records its LLD 23.1.0 byte/layout oracle.

## Traceability, limits and recovery

Executable source: `test/unit/compiler/backend/linker/elf_boot_link_spec.spl`.
Owners: `src/compiler/70.backend/linker/elf/elf_boot_link.spl` and
`src/compiler/70.backend/linker/elf/elf_exec_writer.spl`, as covered by the spec.
This maintenance correction introduces no new feature requirement ID. If a
fixture fails before byte checks with an undefined entry, compare the script's
ENTRY against `llvm-readelf -s` and the checked-in assembly; do not weaken the
relocation assertions. This unit evidence does not qualify whole bootstrap,
native compiler admission, or an executing operating-system image.

## Generation history and selected evidence

Source SHA256: `3794e25b2f627e4c871bf2d323337a60e07936634a23f6d6bedf5596ce07721b`.
The canonical SPL docgen on 2026-10-06 produced one complete manual with zero
stubs; its first 150-second attempt timed out, and its single 420-second
continuation completed without executing tests. The body below is retained
unchanged from that successful generation. This header records reviewed facts.
The previously failed file passed 47/47 examples with zero skips using pinned
Phase1 seed `0f9bfc1` and frozen dependency source `e59027c`; kernel exit0 and
quiescent1 receipts are linked in the accompanying bug document.

# Elf Boot Link Specification

> Tests covering elf_boot_link - PHDRS segments with AT() load addresses, elf_boot_link - section placement, elf_boot_link - script symbols, elf_boot_link - fail-closed, elf_boot_link - FILEHDR / PHDRS keywords, elf_boot_link - MEMORY regions and AT>, elf_boot_link - compound ASSERT, elf_boot_link - region cursors and explicit addresses (lld 23 parity).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Boot Link Specification

## Scenarios

### elf_boot_link - PHDRS segments with AT() load addresses

#### garbage-collects unreachable boot sections and honors KEEP roots

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val object = load_fixture("gc_sections_x64.o")
val collected = elf_boot_link_archives_configured_gc(
    [object], [], plan_of(GC_SCRIPT), RelocArch.X86_64,
    false, [], true)
expect(collected.is_ok()).to_equal(true)

val kept_script = GC_SCRIPT.replace(
    ".text : { *(.text*) }",
    ".text : { KEEP(*(.text.dead_undefined_function)) *(.text*) }")
val kept = elf_boot_link_archives_configured_gc(
    [object], [], plan_of(kept_script), RelocArch.X86_64,
    false, [], true)
expect(kept.is_err()).to_equal(true)
expect(kept.unwrap_err()).to_contain("missing_dead_dependency")
```

</details>

#### strip_output removes the two static symbol-table sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normal = img().bytes
val stripped = elf_boot_link_stripped(objs(), plan_of(BOOT_SCRIPT), RelocArch.AArch64).unwrap()
val normal_shnum = normal[60] | (normal[61] << 8)
val stripped_shnum = stripped[60] | (stripped[61] << 8)
expect(normal_shnum - stripped_shnum).to_equal(2)
expect(stripped.len() < normal.len()).to_equal(true)
```

</details>

#### retained symbols accept placed definitions and reject absent names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = plan_of(BOOT_SCRIPT)
val kept = elf_boot_link_configured(objs(), plan, RelocArch.AArch64, false, ["_start"])
expect(kept.is_ok()).to_equal(true)
val missing = elf_boot_link_configured(objs(), plan, RelocArch.AArch64, false, ["missing_kept"])
expect(missing.is_err()).to_equal(true)
expect(missing.unwrap_err()).to_contain("retained SimpleOS symbol not found")
```

</details>

#### emits exactly the two PHDRS PT_LOADs with FLAGS

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = img().bytes
expect(b[16] | (b[17] << 8)).to_equal(2)            # ET_EXEC
expect(b[56] | (b[57] << 8)).to_equal(2)            # e_phnum
expect(ph32(b, 0, 0)).to_equal(1)                   # PT_LOAD
expect(ph32(b, 0, 4)).to_equal(5)                   # R+X
expect(ph32(b, 1, 0)).to_equal(1)
expect(ph32(b, 1, 4)).to_equal(6)                   # R+W
```

</details>

#### text segment: higher-half VMA, AT() physical address, 64K-congruent offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = img().bytes
expect(ph(b, 0, 8)).to_equal(0x10000)               # p_offset
expect(ph(b, 0, 16)).to_equal(HH + 0x200000)        # p_vaddr
expect(ph(b, 0, 24)).to_equal(0x40200000)           # p_paddr
expect(ph(b, 0, 32)).to_equal(0x58)                 # p_filesz
expect(ph(b, 0, 40)).to_equal(0x58)                 # p_memsz
expect(ph(b, 0, 48)).to_equal(0x10000)              # p_align
```

</details>

#### data segment: AT(ADDR - C) physical address, NOLOAD .bss has no file bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = img().bytes
expect(ph(b, 1, 8)).to_equal(0x11000)
expect(ph(b, 1, 16)).to_equal(HH + 0x201000)
expect(ph(b, 1, 24)).to_equal(0x40201000)
expect(ph(b, 1, 32)).to_equal(0x20)
expect(ph(b, 1, 40)).to_equal(0x28)
```

</details>

#### entry point is _start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = img().bytes
expect(u64_at(b, 24)).to_equal(HH + 0x200000)
```

</details>

### elf_boot_link - section placement

#### applies GNU --wrap reference rewriting before relocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = elf_boot_link_archives_policy(
    objs(), [], plan_of(BOOT_SCRIPT), RelocArch.AArch64,
    false, [], false, ["add_val"])
expect(missing.is_err()).to_equal(true)
expect(missing.unwrap_err()).to_contain("__wrap_add_val")

val aliased = boot_layout_add_defsym(
    plan_of(BOOT_SCRIPT), "__wrap_add_val", "add_val")
val linked = elf_boot_link_archives_policy(
    objs(), [], aliased, RelocArch.AArch64,
    false, [], false, ["add_val"])
expect(linked.is_ok()).to_equal(true)
```

</details>

#### extracts the transitive static-archive closure for a boot image

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linked = elf_boot_link_archives_configured(
    [load_fixture("start_a64.o")], [load_fixture("libchain_a64.a")],
    plan_of(BOOT_SCRIPT), RelocArch.AArch64, false, [])
expect(linked.is_ok()).to_equal(true)
expect(linked.unwrap()[16]).to_equal(2)
```

</details>

#### places sections at the script's addresses with lld's sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = img()
expect(sec_vma(im, ".text")).to_equal(HH + 0x200000)
expect(sec_size(im, ".text")).to_equal(0x58)
expect(sec_vma(im, ".rodata")).to_equal(HH + 0x201000)
expect(sec_size(im, ".rodata")).to_equal(4)
expect(sec_vma(im, ".data")).to_equal(HH + 0x201008)
expect(sec_size(im, ".data")).to_equal(0x18)       # 8 bytes + `. += 0x10`
expect(sec_vma(im, ".bss")).to_equal(HH + 0x201020)
expect(sec_size(im, ".bss")).to_equal(8)
```

</details>

#### emits a PT_TLS image and applies x86-64 local-exec relocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([load_fixture("tls_sections_x64.o")], plan_of(TLS_SCRIPT), RelocArch.X86_64).unwrap()
val b = im.bytes
expect(b[56] | (b[57] << 8)).to_equal(3)
expect(ph32(b, 2, 0)).to_equal(7)                  # PT_TLS
expect(ph32(b, 2, 4)).to_equal(4)                  # PF_R
expect(ph(b, 2, 32)).to_equal(8)                   # initialized image
expect(ph(b, 2, 40)).to_equal(16)                  # initialized + zero-fill
expect(ph(b, 2, 48)).to_equal(8)
expect(sec_vma(im, ".tbss") - sec_vma(im, ".tdata")).to_equal(8)
val text_off = sec_file_off(im, ".text")
expect(u32_at(b, text_off + 5)).to_equal(0xfffffff0) # initialized_tls - TP
expect(u32_at(b, text_off + 14)).to_equal(0xfffffff8) # zero_tls - TP
```

</details>

#### fills a static initial-exec GOT slot with x86-64 TPREL

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([
    load_fixture("tls_import_x64.o"), load_fixture("tls_provider_x64.o")],
    plan_of(TLS_IE_SCRIPT), RelocArch.X86_64).unwrap()
expect(sec_size(im, ".got")).to_equal(8)
expect(u64_at(im.bytes, sec_file_off(im, ".got"))).to_equal(-8)
expect(sec_size(im, ".tdata")).to_equal(8)
```

</details>

#### writes CODE_4 and CODE_6 GOTTPOFF through one SimpleOS TLS slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([load_fixture("code_gottpoff_x64.o")],
    plan_of(TLS_IE_SCRIPT.replace("ENTRY(read_imported_tls)", "ENTRY(_start)")), RelocArch.X86_64).unwrap()
val text_vaddr = sec_vma(im, ".text")
val text_offset = sec_file_off(im, ".text")
val got_vaddr = sec_vma(im, ".got")
val got_offset = sec_file_off(im, ".got")
expect(sec_size(im, ".got")).to_equal(8)
expect(u32_at(im.bytes, text_offset)).to_equal(got_vaddr - text_vaddr)
expect(u32_at(im.bytes, text_offset + 4)).to_equal(got_vaddr - text_vaddr - 4)
expect(u64_at(im.bytes, got_offset)).to_equal(-8)
```

</details>

#### relaxes canonical x86-64 local-dynamic TLS to local-exec

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([load_fixture("tls_local_dynamic_x64.o")],
    plan_of(TLS_SCRIPT), RelocArch.X86_64).unwrap()
val text_off = sec_file_off(im, ".text")
expect(sec_size(im, ".got")).to_equal(-1)
expect(u32_at(im.bytes, text_off + 16)).to_equal(0xfffffff0)
expect(u32_at(im.bytes, text_off + 23)).to_equal(0xfffffff8)
```

</details>

#### relaxes canonical x86-64 global-dynamic TLS to initial-exec

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([
    load_fixture("tls_global_dynamic_x64.o"), load_fixture("tls_provider_x64.o")],
    plan_of(TLS_IE_SCRIPT), RelocArch.X86_64).unwrap()
expect(sec_size(im, ".got")).to_equal(8)
expect(u64_at(im.bytes, sec_file_off(im, ".got"))).to_equal(-8)
```

</details>

#### relaxes canonical x86-64 TLSDESC to initial-exec

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([
    load_fixture("tls_desc_x64.o"), load_fixture("tls_provider_x64.o")],
    plan_of(TLS_IE_SCRIPT), RelocArch.X86_64).unwrap()
val text_off = sec_file_off(im, ".text")
expect(sec_size(im, ".got")).to_equal(8)
expect(u64_at(im.bytes, sec_file_off(im, ".got"))).to_equal(-8)
expect(im.bytes[text_off + 8]).to_equal(0x66)
expect(im.bytes[text_off + 9]).to_equal(0x90)
```

</details>

#### fills a static initial-exec GOT slot with AArch64 variant-I TPREL

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image([
    load_fixture("tls_import_a64.o"), load_fixture("tls_provider_a64.o")],
    plan_of(TLS_IE_SCRIPT), RelocArch.AArch64).unwrap()
expect(sec_size(im, ".got")).to_equal(8)
expect(u64_at(im.bytes, sec_file_off(im, ".got"))).to_equal(16)
expect(sec_size(im, ".tdata")).to_equal(8)
```

</details>

#### places SHN_COMMON through the script COMMON selector as NOBITS storage

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .bss (NOLOAD) : { *(COMMON) }
    /DISCARD/ : { *(.eh_frame) *(.comment) *(.note*) }
}
"""
        val im = elf_boot_link_image([load_fixture("common_x64.o")], plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".bss")).to_equal(48)
        expect(sym(im, "shared_block") % 32).to_equal(0)
        expect(sym(im, "shared_block")).to_equal(sec_vma(im, ".bss"))
```

</details>

#### synthesizes a boot GOT base for R_X86_64_GOTPC32

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
}
"""
        val im = elf_boot_link_image([load_fixture("gotpc32_x64.o")], plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u32_at(im.bytes, 0x1000)).to_equal(sec_vma(im, ".got") - sec_vma(im, ".text"))
```

</details>

#### writes R_X86_64_GOT32 relative to the SimpleOS GOT base

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .data : { *(.data*) }
}
"""
        val im = elf_boot_link_image([load_fixture("got32_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u32_at(im.bytes, 0x1000)).to_equal(0)
```

</details>

#### writes R_X86_64_GOT64 relative to the SimpleOS GOT base

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .data : { *(.data*) }
}
"""
        val im = elf_boot_link_image([load_fixture("got64_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u64_at(im.bytes, 0x1000)).to_equal(0)
```

</details>

#### writes R_X86_64_GOTPCREL64 relative to its SimpleOS patch address

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .data : { *(.data*) }
}
"""
        val im = elf_boot_link_image([load_fixture("gotpcrel64_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u64_at(im.bytes, 0x1000)).to_equal(
            sec_vma(im, ".got") - sec_vma(im, ".text"))
```

</details>

#### writes R_X86_64_CODE_4_GOTPCRELX relative to its SimpleOS patch address

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .data : { *(.data*) }
}
"""
        val im = elf_boot_link_image([load_fixture("code4_gotpcrelx_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u32_at(im.bytes, 0x1000)).to_equal(
            sec_vma(im, ".got") - sec_vma(im, ".text"))
```

</details>

#### writes R_X86_64_GOTPC64 against the synthesized SimpleOS GOT base

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
}
"""
        val im = elf_boot_link_image([load_fixture("gotpc64_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u64_at(im.bytes, 0x1000)).to_equal(
            sec_vma(im, ".got") - sec_vma(im, ".text"))
```

</details>

#### writes R_X86_64_GOTOFF64 from a data address to the SimpleOS GOT base

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .data : { *(.data*) }
}
"""
        val im = elf_boot_link_image([load_fixture("gotoff64_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u64_at(im.bytes, 0x1000)).to_equal(
            sec_vma(im, ".data") - sec_vma(im, ".got"))
```

</details>

#### writes R_X86_64_PLTOFF64 from a function address to the SimpleOS GOT base

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
}
"""
        val im = elf_boot_link_image([load_fixture("pltoff64_x64.o")],
            plan_of(script), RelocArch.X86_64).unwrap()
        expect(sec_size(im, ".got")).to_equal(8)
        expect(u64_at(im.bytes, 0x1000)).to_equal(
            sec_vma(im, ".text") + 9 - sec_vma(im, ".got"))
```

</details>

#### writes R_X86_64_SIZE32 and SIZE64 from the winning symbol extent

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
        val script = """ENTRY(_start)
SECTIONS {
    . = 0x100000;
    .text : { *(.text*) }
    .data : { *(.data*) }
}
"""
        val im = elf_boot_link_image([load_fixture("symbol_size_x64.o"),
            load_fixture("symbol_size_def_x64.o")], plan_of(script), RelocArch.X86_64).unwrap()
        val data_off = sec_file_off(im, ".data")
        expect(u32_at(im.bytes, data_off)).to_equal(13)
        expect(u64_at(im.bytes, data_off + 8)).to_equal(13)
```

</details>

#### relocated .text bytes equal ld.lld --no-relax

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = img().bytes
var got: [i64] = []
var i: i64 = 0
while i < LLD_TEXT.len():
    got = got.push(b[0x10000 + i])
    i = i + 1
expect(got).to_equal(LLD_TEXT)
```

</details>

#### .data carries the initialised value followed by the pad

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = img().bytes
expect(u64_at(b, 0x11008)).to_equal(2)
expect(u64_at(b, 0x11010)).to_equal(0)
```

</details>

### elf_boot_link - script symbols

#### location-counter symbols follow the replayed order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = img()
expect(sym(im, "_kernel_start")).to_equal(HH + 0x200000)
expect(sym(im, "_data_end")).to_equal(HH + 0x201020)
expect(sym(im, "_bss_start")).to_equal(HH + 0x201020)
expect(sym(im, "_bss_end")).to_equal(HH + 0x201028)
expect(sym(im, "_kernel_end")).to_equal(HH + 0x201028)
```

</details>

#### PROVIDE defines only referenced symbols and never overrides an object definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = img()
expect(sym(im, "_used_provide")).to_equal(0x1234)
expect(sym(im, "_probe")).to_equal(0x1235)
expect(has_sym(im, "_unused_provide")).to_equal(false)
expect(sym(im, "base")).to_equal(HH + 0x201008)
```

</details>

#### --defsym is a top-level assignment evaluated after layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = boot_layout_add_defsym(plan_of(BOOT_SCRIPT), "_alias", "add_val")
val im = elf_boot_link_image(objs(), plan, RelocArch.AArch64).unwrap()
expect(sym(im, "_alias")).to_equal(HH + 0x20003c)
```

</details>

### elf_boot_link - fail-closed

#### a failing ASSERT is an Err carrying its message

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = BOOT_SCRIPT.replace("<= 0x100000", "<= 0x10")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err().contains("kernel too big")).to_equal(true)
```

</details>

#### an allocatable input no statement places is an orphan Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = BOOT_SCRIPT.replace("*(.data*)", "*(.nothing)")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err().contains("orphan")).to_equal(true)
```

</details>

#### an undefined entry symbol is an Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = BOOT_SCRIPT.replace("ENTRY(_start)", "ENTRY(no_such_entry)")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err().contains("no_such_entry")).to_equal(true)
```

</details>

### elf_boot_link - FILEHDR / PHDRS keywords

#### PT_PHDR describes the table inside the FILEHDR load

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = elf_boot_link(objs(), plan_of(HDR_SCRIPT), RelocArch.AArch64).unwrap()
expect(b[56] | (b[57] << 8)).to_equal(3)
expect(ph32(b, 0, 0)).to_equal(6)                   # PT_PHDR
expect(ph(b, 0, 8)).to_equal(0x40)
expect(ph(b, 0, 16)).to_equal(0x400040)
expect(ph(b, 0, 32)).to_equal(0xa8)
```

</details>

#### the FILEHDR load starts at file offset 0 at the load base

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = elf_boot_link(objs(), plan_of(HDR_SCRIPT), RelocArch.AArch64).unwrap()
expect(ph(b, 1, 8)).to_equal(0)
expect(ph(b, 1, 16)).to_equal(0x400000)
expect(ph(b, 1, 32)).to_equal(0x144)
expect(ph(b, 2, 8)).to_equal(0x10000)
expect(ph(b, 2, 16)).to_equal(0x410000)
expect(ph(b, 2, 32)).to_equal(8)
expect(ph(b, 2, 40)).to_equal(0x10)
```

</details>

### elf_boot_link - MEMORY regions and AT>

#### allocates .data's load address from the ROM cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image(objs(), plan_of(REGION_SCRIPT), RelocArch.AArch64).unwrap()
expect(sec_vma(im, ".rodata")).to_equal(0x100058)
expect(sec_vma(im, ".data")).to_equal(0x200000)
expect(sym(im, "_sidata")).to_equal(0x100060)
expect(sec_vma(im, ".bss")).to_equal(0x200008)
```

</details>

#### emits lld's four PT_LOADs (LMA change and AT> reset split segments)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = elf_boot_link(objs(), plan_of(REGION_SCRIPT), RelocArch.AArch64).unwrap()
expect(b[56] | (b[57] << 8)).to_equal(4)
expect(ph(b, 1, 8)).to_equal(0x10058)
expect(ph(b, 2, 8)).to_equal(0x20000)
expect(ph(b, 2, 16)).to_equal(0x200000)
expect(ph(b, 2, 24)).to_equal(0x100060)
expect(ph(b, 3, 24)).to_equal(0x200008)
expect(ph(b, 3, 32)).to_equal(0)
```

</details>

#### a section overflowing its region is an Err naming both

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = REGION_SCRIPT.replace("ORIGIN = 0x100000, LENGTH = 0x10000", "ORIGIN = 0x100000, LENGTH = 0x50")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_contain("section .text will not fit in region ROM: overflowed by 8 bytes")
```

</details>

#### overlapping section VMAs are an Err naming both

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = REGION_SCRIPT.replace(".bss : { *(.bss*) } > RAM", ".bss 0x200004 : { *(.bss*) }")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_contain(".data virtual address range overlaps with .bss")
```

</details>

### elf_boot_link - compound ASSERT

#### a false compound ASSERT is an Err (&& binds looser than <=)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = BOOT_SCRIPT.replace("_kernel_end - _kernel_start <= 0x100000", "_kernel_end > _kernel_start && _kernel_end - _kernel_start <= 0x10")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_contain("kernel too big")
```

</details>

### elf_boot_link - region cursors and explicit addresses (lld 23 parity)

#### a region used as both VMA and AT> region advances once

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image(objs(), plan_of(SAME_REGION_SCRIPT), RelocArch.AArch64).unwrap()
expect(sec_vma(im, ".rodata")).to_equal(0x200058)
expect(sec_vma(im, ".data")).to_equal(0x200060)
expect(sec_vma(im, ".bss")).to_equal(0x200068)
```

</details>

#### a NOBITS section with AT> still advances the load region

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image(objs(), plan_of(NOBITS_AT_SCRIPT), RelocArch.AArch64).unwrap()
expect(im.sec_lmas[1]).to_equal(0x100058)
expect(sec_vma(im, ".rodata")).to_equal(0x100068)
```

</details>

#### an explicit address is kept even with ALIGN() after the colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val im = elf_boot_link_image(objs(), plan_of(EXPLICIT_ADDR_SCRIPT), RelocArch.AArch64).unwrap()
expect(sec_vma(im, ".text")).to_equal(0x200001)
expect(sec_size(im, ".text")).to_equal(0x5b)
expect(sec_vma(im, ".rodata")).to_equal(0x200201)
```

</details>

#### a top-of-memory region overflows at the right section, reported unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = elf_boot_link(objs(), plan_of(TOP_REGION_SCRIPT), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_contain("section .data will not fit in region HI: overflowed by 8 bytes")
```

</details>

#### origin + length wrapping to 0 is rejected exactly as ld.lld 23 does

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = TOP_REGION_SCRIPT.replace("LENGTH = 0x60", "LENGTH = 0x80000000")
val r = elf_boot_link(objs(), plan_of(script), RelocArch.AArch64)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_contain("section .text will not fit in region HI: overflowed by 18446744071562068056 bytes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/linker/elf_boot_link_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering elf_boot_link - PHDRS segments with AT() load addresses, elf_boot_link - section placement, elf_boot_link - script symbols, elf_boot_link - fail-closed, elf_boot_link - FILEHDR / PHDRS keywords, elf_boot_link - MEMORY regions and AT>, elf_boot_link - compound ASSERT, elf_boot_link - region cursors and explicit addresses (lld 23 parity).
- elf_boot_link - PHDRS segments with AT() load addresses
- elf_boot_link - section placement
- elf_boot_link - script symbols
- elf_boot_link - fail-closed
- elf_boot_link - FILEHDR / PHDRS keywords
- elf_boot_link - MEMORY regions and AT>
- elf_boot_link - compound ASSERT
- elf_boot_link - region cursors and explicit addresses (lld 23 parity)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
