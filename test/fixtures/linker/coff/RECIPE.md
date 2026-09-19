# COFF/PE linker fixtures (lane E1)

Tiny freestanding x86_64 Windows COFF objects for the internal COFF→PE linker
specs (`test/01_unit/compiler/backend/linker/coff_*_spec.spl` and
`pe_exec_writer_spec.spl`), plus one **lld-link golden image** the writer's
structural parity is measured against.

Produced with `clang version 23.1.0 (ea7d852a70e8)`, `llvm-ar` and `lld-link`
from `/home/yoon/dev/llvm/install/bin`, run from this directory. The build host
is **aarch64 Linux**: clang cross-compiles to `x86_64-windows-msvc` and
`lld-link` cross-links, with no MSVC headers and no CRT — every object is
`-ffreestanding -nostdlib`, which is the whole reason the programs only compute
and never call an imported function.

```
CF="-c -O1 -ffreestanding -fno-asynchronous-unwind-tables -fno-unwind-tables --target=x86_64-windows-msvc"
clang $CF start_x64.c  -o start_x64.obj
clang $CF lib_x64.c    -o lib_x64.obj
clang $CF mid_x64.c    -o mid_x64.obj
clang $CF leaf_x64.c   -o leaf_x64.obj
clang $CF unused_x64.c -o unused_x64.obj
clang $CF chain_x64.c  -o chain_x64.obj
clang -c --target=x86_64-windows-msvc secrel_x64.s -o secrel_x64.obj
llvm-ar rcs libchain_x64.lib mid_x64.obj leaf_x64.obj unused_x64.obj
lld-link /entry:entry /subsystem:console /nodefaultlib /timestamp:0 \
         /out:hello_x64.lld.exe start_x64.obj lib_x64.obj
lld-link /entry:anchor /subsystem:console /nodefaultlib /timestamp:0 \
         /out:secrel_x64.lld.exe secrel_x64.obj
lld-link /entry:chain_entry /subsystem:console /nodefaultlib /timestamp:0 \
         /out:chain_x64.lld.exe chain_x64.obj libchain_x64.lib
```

There are THREE goldens, and the internal engine is byte-identical to all
three: `hello_x64.lld.exe` (3072 B, 4 sections), `secrel_x64.lld.exe` (2048 B,
2 sections) and `chain_x64.lld.exe` (1024 B, 1 section, archive fixpoint —
`lld-link` accepts the `llvm-ar` GNU-format `.lib` directly). The chain golden
also pins member SELECTION and ORDER: a fixpoint that pulled `unused_x64.obj`,
or placed `mid_fn`/`leaf_fn` in a different order, would change every REL32
displacement and diverge.

`/timestamp:0` is what makes the golden reproducible — lld-link's default
`TimeDateStamp` is `time()`. `/Brepro` is deliberately NOT used: it would add a
REPRO debug directory entry and a data directory this lane does not model.

## Relocations exercised (`llvm-readobj --relocs`)

| object | section | relocations |
|---|---|---|
| start_x64.obj | .text | REL32 `add_val` (+0xa), REL32 `base` (+0x10), REL32 `msg_ptr` (+0x17) |
| start_x64.obj | .data | ADDR64 `msg` (+0x0) |
| lib_x64.obj | .text | REL32 `scratch`, REL32 `base` |
| mid_x64.obj | .text | REL32 `leaf_fn` (archive chain) |
| secrel_x64.obj | .rdata | SECREL `anchor` (+0x0), SECTION `anchor` (+0x4), ADDR32NB `anchor` (+0x8) |

`secrel_x64.s` is hand-written assembly on purpose: **clang never emits SECREL,
SECTION or ADDR32NB from C on this target**, and the `.secrel32` / `.secidx` /
`@IMGREL` directives are the only way to produce them here.

**IMAGE_REL_AMD64_REL32_1 … REL32_5 have no fixture, and cannot have one from
this toolchain.** LLVM's COFF assembler encodes `movl $imm, sym(%rip)` and
friends as a plain `REL32` with the instruction-length bias pre-folded into the
displacement field rather than emitting `REL32_4` (verified by
`llvm-readobj --relocs` on a hand-written `.s` probe). Their value formulas are
covered by `coff_reloc_oracle_spec.spl` only; nothing in this tree exercises
them end to end.

## Golden image facts (`llvm-readobj --file-headers --sections --coff-basereloc`)

`hello_x64.lld.exe`, 3072 bytes, 4 sections, `TimeDateStamp` 0:

| | |
|---|---|
| Machine / Magic | `0x8664` / `PE32+` (`0x20b`) |
| Characteristics | `0x22` (EXECUTABLE_IMAGE \| LARGE_ADDRESS_AWARE) |
| OptionalHeaderSize | 240, `NumberOfRvaAndSize` 16 |
| ImageBase / SectionAlignment / FileAlignment | `0x140000000` / `0x1000` / `0x200` |
| SizeOfHeaders / SizeOfImage | `0x400` / `0x5000` |
| AddressOfEntryPoint / BaseOfCode | `0x1000` / `0x1000` |
| Subsystem | `IMAGE_SUBSYSTEM_WINDOWS_CUI` (3), OS/Subsystem version 6.0 |
| DllCharacteristics | `0x8160` (HIGH_ENTROPY_VA \| DYNAMIC_BASE \| NX_COMPAT \| TERMINAL_SERVER_AWARE) |
| Stack / heap reserve, commit | 0x100000 / 0x1000 both |
| Linker version | 14.0 |

| # | section | VirtualSize | RVA | RawDataSize | PointerToRawData | Characteristics |
|---|---|---|---|---|---|---|
| 1 | `.text` | `0x3f` | `0x1000` | 512 | `0x400` | `0x60000020` |
| 2 | `.rdata` | `0x4` | `0x2000` | 512 | `0x600` | `0x40000040` |
| 3 | `.data` | `0x10` | `0x3000` | 512 | `0x800` | `0xc0000040` |
| 4 | `.reloc` | `0xc` | `0x4000` | 512 | `0xa00` | `0x42000040` |

Input `.bss` is folded into `.data` (`.data` VirtualSize `0x10` = `msg_ptr` 8 +
`base` 4 + `scratch` 4), and `BaseRelocationTable` is RVA `0x4000` size `0xc`:
one `DIR64` entry at RVA `0x3000` (the `msg_ptr` pointer) plus one `ABSOLUTE`
pad entry, because a `.reloc` block's entry count must be even.

The specs depend on the exact offsets in the tables above (e.g. the REL32 call
at `.text+0xa`); if these objects are rebuilt with a different compiler, the
specs' constants must be regenerated from a fresh `llvm-readobj` dump.

## Not proven here

There is **no wine and no Windows host on this machine**, so none of these
images has ever been executed. Every claim in the COFF/PE specs is structural
(headers, section table, data directories, base relocations, patched bytes) and
measured against `lld-link` as the oracle. Runnability on Windows is unproven.

## SizeOfHeaders is reserved from the PRE-removal section count

`secrel_x64.lld.exe` has **2** sections but `SizeOfHeaders` `0x400`, while
`chain_x64.lld.exe` has 1 section and `0x200`. Deriving `SizeOfHeaders` from
the final `SectionCount` gives `0x200` for secrel and then every section's
`PointerToRawData` is off by `0x200`. lld-link sizes the headers over the
output sections it has *created* — always including a `.reloc`, even when it
ends up empty — and removes the empty ones afterwards:

| image | reserved (pre-removal) | headers | SizeOfHeaders | final SectionCount |
|---|---|---|---|---|
| hello_x64 | 4 (.text .rdata .data .reloc) | 544 | `0x400` | 4 |
| secrel_x64 | 4 (.text .rdata .data .reloc) | 544 | `0x400` | 2 |
| chain_x64 | 3 (.text .data .reloc) | 504 | `0x200` | 1 |
| a pure-`.bss` probe | 3 (.text .data .reloc) | 504 | `0x200` | 2 |

`coff_layout.coff_reserved_out_count` reproduces this, which is what makes the
engine a drop-in for lld-link rather than only a valid-PE writer.

## Review fixtures (three cases where lld-link contradicted us)

```
clang -c --target=x86_64-windows-msvc absuse_x64.s  -o absuse_x64.obj
clang -c --target=x86_64-windows-msvc absdef_x64.s  -o absdef_x64.obj
clang -c --target=x86_64-windows-msvc absuse2_x64.s -o absuse2_x64.obj
lld-link /entry:ab_entry /subsystem:console /nodefaultlib /timestamp:0 \
         /out:absuse_x64.lld.exe absuse_x64.obj absdef_x64.obj
# wrdata_x64.obj is secrel_x64.obj with byte 179 patched 0x40 -> 0xC0, i.e.
# its .rdata Characteristics 0x40100040 -> 0xC0100040 (MEM_WRITE set). The
# assembler will not emit a writable .rdata, so the flag is set by patching.
cp secrel_x64.obj wrdata_x64.obj
printf '\300' | dd of=wrdata_x64.obj bs=1 seek=179 count=1 conv=notrunc
lld-link /entry:anchor /subsystem:console /nodefaultlib /timestamp:0 \
         /out:wrdata_x64.lld.exe wrdata_x64.obj
clang -c --target=x86_64-windows-msvc wrdata2_x64.s -o wrdata2_x64.obj
printf '\300' | dd of=wrdata2_x64.obj bs=1 seek=179 count=1 conv=notrunc
```

| fixture | what it pins |
|---|---|
| `absuse_x64` + `absdef_x64` | an ADDR64 to an ABSOLUTE symbol gets **no** base relocation — the golden is 1536 B / 2 sections with an EMPTY base-reloc table. We emitted 3 sections / 2048 B with a DIR64 at `0x2000`, so under dynamic base the loader added the image delta to the constant `0x1234` |
| `absuse2_x64` | a SECREL to an ABSOLUTE symbol: `lld-link` exits 1, "SECREL relocation cannot be applied to absolute symbols". We linked it as `0x1234 - 0` |
| `wrdata_x64` | output flags come from the input **Characteristics**, not the section NAME: lld reports `.rdata` `0xC0000040`, we reported `0x40000040` and the image would fault on the first write |
| `wrdata2_x64` | paired with `secrel_x64.obj` (no symbol in common), two inputs merging to one output name with different masked Characteristics |

`absuse_x64.lld.exe` and `wrdata_x64.lld.exe` are goldens 4 and 5; the engine is
byte-identical to all five.

The `printf '\300'` above is OCTAL on purpose: `\xNN` is not POSIX and `dash`
(`/bin/sh` on Debian and Ubuntu) writes a literal `\`, `x`, `c`, `0` for it, so
the recipe as first written did not reproduce the committed objects under
`sh`. Verified: `dash -c "printf '\300'" | od -An -tx1` prints `c0`.

## SECTION against an absolute symbol (goldens 6 and 7)

```
clang -c --target=x86_64-windows-msvc secidx_x64.s  -o secidx_x64.obj
clang -c --target=x86_64-windows-msvc secidx2_x64.s -o secidx2_x64.obj
lld-link /entry:ab_entry /subsystem:console /nodefaultlib /timestamp:0 \
         /out:secidx_x64.lld.exe  secidx_x64.obj  absdef_x64.obj
lld-link /entry:ab_entry /subsystem:console /nodefaultlib /timestamp:0 \
         /out:secidx2_x64.lld.exe secidx2_x64.obj absdef_x64.obj
```

lld does NOT refuse `.secidx` against an absolute symbol — it exits 0 and
writes `numOutputSections + 1`. `secidx_x64` has 2 output sections and the
value `0x0003`; `secidx2_x64` adds an ADDR64 so a `.reloc` exists, making 3
sections and the value `0x0004` — i.e. the synthesized `.reloc` is counted.

These two also pinned a placement rule the earlier fixtures never exercised:
**a zero-size input section is still placed, and its alignment advances the
output size.** `secidx_x64.obj`'s 2-byte `.data` plus `absdef_x64.obj`'s 0-byte
4-aligned `.data` give lld a 4-byte output `.data`, not 2. Sections that are
still empty after every contribution are then removed from the table, which is
lld's create-then-remove order and is why `SizeOfHeaders` is reserved from the
pre-removal count.

There are SEVEN goldens in total and the engine is byte-identical to all of
them: `hello_x64`, `secrel_x64`, `chain_x64`, `absuse_x64`, `wrdata_x64`,
`secidx_x64` and `secidx2_x64`.
