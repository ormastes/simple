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
clang --target=aarch64-linux-gnu -c -O1 -fPIE -fno-asynchronous-unwind-tables -fno-unwind-tables hello_libm.c -o hello_libm_a64.o
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

`hello_libm_a64.o` (lane F1) additionally calls `sqrt`, so it links only when the
linker resolves a library SEARCH name: `NativeLinkConfig.libraries = ["m"]` plus
`library_paths`, or `-lm` externally. On glibc hosts `libm.so` is a GNU ld script
(`GROUP ( /lib/<triple>/libm.so.6 AS_NEEDED ( ... ) )`), not an ELF file, so
resolving it exercises the internal engine's ld-script member handling. It prints
`sqrt=42` and exits 42. Linked by `native_linking_internal_spec`.

`main_int_a64.o` + `libshadowatoi_a64.so` (lane F1, round 2) prove DT_NEEDED
ORDER rather than the set. The library defines `atoi()` returning 42; libc's
returns 1; `main_int.c` calls it through a global with `-fno-builtin` so the
call cannot be constant-folded. The DT_NEEDED *set* is identical whichever
order the linker emits, so only the exit status distinguishes them: 42 when the
`-l` library precedes libc (ld.lld's order), 1 when libc precedes it.

```
clang --target=aarch64-linux-gnu -shared -fPIC -Wl,-soname,libshadowatoi_a64.so shadow_atoi.c -o libshadowatoi_a64.so
clang --target=aarch64-linux-gnu -c -O1 -fno-builtin -fPIE -fno-asynchronous-unwind-tables -fno-unwind-tables main_int.c -o main_int_a64.o
```

`libshadowatoi_a64.so` must keep a bare `.so` name — `-l<name>` searches for
exactly `lib<name>.so`, which is the point of the fixture — so unlike the
sibling `.so.1` fixtures it is matched by `.gitignore:23 *.so` and was added
with `git add -f`. If it is ever regenerated, re-add it the same way or the
DT_NEEDED-order spec loses its library.
