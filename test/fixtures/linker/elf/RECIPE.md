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
