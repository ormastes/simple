# ELF linker fixtures (lane A7 slice 1)

Tiny freestanding ET_REL objects for the internal static ELF linker specs
(`test/01_unit/compiler/backend/linker/elf_{exec_writer,archive_closure,static_link}_spec.spl`).
Each program writes `hi\n` and exits with status 42 (40 + `base` = 2).

Produced with `clang version 23.1.0 (ea7d852a70e8)` and `llvm-ar` from the same
install, run from this directory:

```
CF="-c -O1 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $CF start_a64.c  -o start_a64.o
clang --target=aarch64-linux-gnu $CF lib_a64.c    -o lib_a64.o
clang --target=aarch64-linux-gnu $CF mid_a64.c    -o mid_a64.o
clang --target=aarch64-linux-gnu $CF leaf_a64.c   -o leaf_a64.o
clang --target=aarch64-linux-gnu $CF unused_a64.c -o unused_a64.o
llvm-ar rcs libchain_a64.a mid_a64.o leaf_a64.o unused_a64.o
clang --target=x86_64-linux-gnu  $CF start_x64.c  -o start_x64.o
clang --target=x86_64-linux-gnu  $CF lib_x64.c    -o lib_x64.o
```

Relocations exercised (`llvm-readelf -r`):

| object | relocations |
|---|---|
| start_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (msg), CALL26 (add_val) |
| lib_a64.o | ADR_PREL_PG_HI21 + LDST64_ABS_LO12_NC (base, scratch) |
| mid_a64.o | JUMP26 (tail call to leaf_fn) |
| start_x64.o | R_X86_64_32 (msg), PLT32 (add_val) |
| lib_x64.o | PC32 (base, scratch) |

The specs depend on the exact byte offsets noted in them (e.g. the CALL26 at
`_start+0x24`, x86_64 `call` rel32 at `.text+0x1d`); regenerate the specs'
constants if these objects are rebuilt with a different compiler.

## Slice 2 fixtures (GOT, static PIE, dynamic libc)

Same compiler, run from this directory:

```
PIC="-c -O1 -ffreestanding -fPIC -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
PIE="-c -O1 -ffreestanding -fPIE -fvisibility=hidden -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $PIC start_a64.c -o pic_start_a64.o
clang --target=aarch64-linux-gnu $PIC lib_a64.c   -o pic_lib_a64.o
clang --target=x86_64-linux-gnu  $PIC start_x64.c -o pic_start_x64.o
clang --target=x86_64-linux-gnu  $PIC lib_x64.c   -o pic_lib_x64.o
clang --target=aarch64-linux-gnu $PIE -fdirect-access-external-data start_a64.c -o pie_start_a64.o
clang --target=aarch64-linux-gnu $PIE lib_a64.c   -o pie_lib_a64.o
clang --target=x86_64-linux-gnu  $PIE start_x64.c -o pie_start_x64.o
clang --target=x86_64-linux-gnu  $PIE lib_x64.c   -o pie_lib_x64.o
clang --target=aarch64-linux-gnu -c -O1 -fPIE -fno-asynchronous-unwind-tables -fno-unwind-tables hello_libc.c -o hello_libc_a64.o
```

| object | relocations |
|---|---|
| pic_start_a64.o | ADR_GOT_PAGE (+4) + LD64_GOT_LO12_NC (+0x10) (msg), CALL26 (add_val) |
| pic_lib_a64.o | ADR_GOT_PAGE + LD64_GOT_LO12_NC (base, scratch) — pairs not adjacent, so ld.lld keeps the GOT |
| pic_start_x64.o | REX_GOTPCRELX (msg, `mov` at .text+1, opcode byte +2), PLT32 (add_val) |
| pic_lib_x64.o | REX_GOTPCRELX (scratch, base) |
| pie_start_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (msg), CALL26 (add_val) |
| pie_lib_a64.o | ADR_PREL_PG_HI21 + LDST64_ABS_LO12_NC (base, scratch) |
| pie_start_x64.o | REX_GOTPCRELX (msg, relaxed to `lea`), PLT32 (add_val) |
| pie_lib_x64.o | PC32 (scratch, base) |
| hello_libc_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (.rodata.str1.1), CALL26 (puts, exit); `main` is in `.text.unlikely.` |

`hello_libc_a64.o` is linked by `elf_dynamic_link_spec` and `link_engine_external_spec`
together with the HOST glibc startup objects and `libc.so.6` from
`/usr/lib/aarch64-linux-gnu` (not vendored here), so those specs need an aarch64
Linux host with glibc. It prints `hi from libc` and exits 42.

## Lane B2 fixtures (.gnu.hash oracle, x86_64 dynamic)

Same compiler + `ld.lld` from the same install, run from this directory. The
shared objects carry a `.1` suffix because the repo `.gitignore` drops `*.so`:

```
PIC="-c -O1 -ffreestanding -fPIC -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $PIC gnu_hash_syms.c -o gnu_hash_syms_a64.o
ld.lld -shared --soname libgnuhash.so --hash-style=both -o libgnuhash_a64.so.1 gnu_hash_syms_a64.o
ld.lld -shared --soname libadd_x64.so --hash-style=both -o libadd_x64.so.1 pic_lib_x64.o
```

| file | role |
|---|---|
| libgnuhash_a64.so.1 | `.gnu.hash` oracle: 11 exports -> 2 buckets, 4 bloom words, symoffset 1 (`llvm-readelf --gnu-hash-table`); `elf_gnu_hash_spec` rebuilds it byte for byte from its `.dynsym` names |
| libadd_x64.so.1 | x86_64 DSO exporting add_val / msg / base / scratch (soname `libadd_x64.so`); `elf_x64_dynamic_spec` links `pic_start_x64.o` against it: add_val via PLT32 -> PLT1 + R_X86_64_JUMP_SLOT, msg via REX_GOTPCRELX (kept as `mov`, import) -> .got + R_X86_64_GLOB_DAT |

The x86_64 dynamic outputs are compared with
`ld.lld --dynamic-linker /lib64/ld-linux-x86-64.so.2 [-pie] pic_start_x64.o libadd_x64.so.1`
(`llvm-readelf -l -S -d -r`, `llvm-objdump -d --section=.plt`). They are never
executed: this aarch64 host has no x86_64 glibc or ld-linux-x86-64.so.2.

## Lane C1 fixture (RELRO)

`relro_a64.o` gives a dynamic PIE one input section for every PT_GNU_RELRO
member ld.lld places: `.init_array` (constructor), `.fini_array` (destructor),
`.data.rel.ro` (a `const` table of code pointers), plus `.got`/`.dynamic` from
the link itself and a non-RELRO `.data`/`.got.plt`/`.bss`. It prints
`relro ok` and exits 42. Same compiler as above, run from this directory:

```
clang --target=aarch64-linux-gnu -c -O1 -fPIE -fno-asynchronous-unwind-tables \
    -fno-unwind-tables relro_a64.c -o relro_a64.o
```

RELRO oracle for `elf_relro_spec` (needs the host glibc startup objects, like
`hello_libc_a64.o`):

```
ld.lld-23 -pie -dynamic-linker /lib/ld-linux-aarch64.so.1 \
    /usr/lib/aarch64-linux-gnu/Scrt1.o /usr/lib/aarch64-linux-gnu/crti.o \
    relro_a64.o /usr/lib/aarch64-linux-gnu/crtn.o \
    /usr/lib/aarch64-linux-gnu/libc.so.6 -o rpie_lld
```

## Lane C1 fixture (--gc-sections)

`gc_a64.o` is built with `-ffunction-sections -fdata-sections`, so every
function and datum is its own input section: a live chain from `_start`
(`gc_add` -> `gc_leaf`, `gc_msg`, `gc_base`, `gc_scratch`), an unreferenced
dead chain (`gc_dead` -> `gc_dead_leaf`, `gc_dead_msg`, `gc_dead_base`,
`gc_dead_scratch`), an `SHF_GNU_RETAIN` function (`gc_retained`), a `.init`
function (`gc_in_init`) and a function reachable only through `.init_array`
(`gc_ctor`). It writes `gc\n` and exits 42.

```
clang --target=aarch64-linux-gnu -c -O1 -ffreestanding -fno-pic \
    -ffunction-sections -fdata-sections -fno-asynchronous-unwind-tables \
    -fno-unwind-tables -nostdlib gc_a64.c -o gc_a64.o
```

GC oracle for `elf_gc_sections_spec`:

```
ld.lld-23 -static -e _start --gc-sections --print-gc-sections gc_a64.o -o gcy
ld.lld-23 -static -e _start gc_a64.o -o gcn
```

## Lane C1 fixtures (SHF_MERGE string merge)

`merge_a_a64.o` and `merge_b_a64.o` share the literals `hi\n` and `dup\n` and
each add one of their own, so a `-O1` link must drop two duplicates. `_start`
compares `a_dup()` with `b_dup()` and adds 2 only when they merged to one
address: exit 42 means merged, exit 40 means not. Same compiler as above:

```
CF="-c -O2 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $CF merge_a_a64.c -o merge_a_a64.o
clang --target=aarch64-linux-gnu $CF merge_b_a64.c -o merge_b_a64.o
```

(`-fmerge-constants` is accepted by gcc but warned-and-ignored by this clang;
clang emits `.rodata.str1.1` as `SHF_MERGE|SHF_STRINGS` regardless, which is
what the merge path consumes.)

Merge oracle for `elf_merge_strings_spec`:

```
ld.lld-23 -static -e _start -O1 merge_a_a64.o merge_b_a64.o -o mrg1   # .rodata 0x19, exit 42
ld.lld-23 -static -e _start -O0 merge_a_a64.o merge_b_a64.o -o mrg0   # .rodata 0x22, exit 40
```

### Wide-literal, end-of-section and demotion fixtures (lane C1 review)

`merge_wide_a64.o` + `merge_wideb_a64.o` share one `L"wide"` literal in
`.rodata.str4.4` (`SHF_MERGE|SHF_STRINGS`, `sh_entsize 4`); ld.lld MERGES
multi-byte strings (`splitStrings` -> `findNull` scans entsize-sized NUL
units), so `-O1` gives one copy and exit 42, `-O0` two copies and exit 40.
`merge_strend_a64.o` defines a global at the very END of a merged section
(`st_value == sh_size`), which ld.lld accepts (its bound is `offset > size`).
`merge_relin_a64.o` has `.rodata.cst8` holding `.quad target`, i.e. a
relocation INTO a merge section, which ld.lld demotes to a regular input
section. All three exit 42.

```
CF="-c -O2 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
for f in merge_wide_a64 merge_wideb_a64 merge_strend_a64 merge_relin_a64; do
  clang --target=aarch64-linux-gnu $CF $f.c -o $f.o
done
ld.lld-23 -static -e _start -O1 merge_wide_a64.o merge_wideb_a64.o   # .rodata 0x14 es 4, exit 42
ld.lld-23 -static -e _start -O0 merge_wide_a64.o merge_wideb_a64.o   # .rodata 0x28 es 4, exit 40
ld.lld-23 -static -e _start -O1 merge_strend_a64.o                   # links, exit 42
ld.lld-23 -static -e _start -O1 merge_relin_a64.o                    # .rodata 0x08 AM es 8
ld.lld-23 -static -e _start -O1 merge_relin_a64.o merge_b_a64.o      # .rodata 0x19 es 0
```
