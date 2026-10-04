# SimpleOS x86_64 user-link fixtures

Inputs for `test/01_unit/compiler/backend/linker/simpleos_internal_entry_spec.spl`,
which drives `link_simpleos_internal` the way
`src/compiler/70.backend/backend/simpleos_native_linkers.spl` does for a
`x86_64-unknown-simpleos` user program.

- `simpleos_user.ld` — byte-for-byte copy of the sysroot script
  `build/os/sysroot/share/simpleos/simpleos.ld` written by
  `src/os/port/llvm/sysroot.shs` (`ENTRY(_start)`, text at `0x10000000`).
- `crt0_x64.s` — minimal crt0 with a GLOBAL FUNC `_start` in `.text`.
- `main_x64.c` — `main` plus a GLOBAL helper and a LOCAL `.data` object.

Produced with `Ubuntu clang version 21.1.8`, run from this directory:

```
clang --target=x86_64-unknown-none-elf -c crt0_x64.s -o crt0_x64.o
clang --target=x86_64-unknown-none-elf -c -O1 -ffreestanding -fno-pic -fno-stack-protector \
    -fno-asynchronous-unwind-tables -fno-unwind-tables main_x64.c -o main_x64.o
```

Cross-check: `ld.lld -T simpleos_user.ld -nostdlib -static --gc-sections
crt0_x64.o main_x64.o` reports `Entry point address: 0x10000000`.
