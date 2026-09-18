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
