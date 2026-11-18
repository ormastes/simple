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

## aarch64

- `simpleos_user_a64.ld` — copy of the script written by
  `scripts/os/simpleos-sysroot-aarch64.shs` (`ENTRY(_start)`, text at `0x50000000`).
- `crt0_a64.s`, `main_a64.c` (same C as `main_x64.c`).

Produced with `Ubuntu clang version 18.1.3`:

```
clang --target=aarch64-unknown-none-elf -c crt0_a64.s -o crt0_a64.o
clang --target=aarch64-unknown-none-elf -c -O1 -ffreestanding -fno-pic -fno-stack-protector \
    -fno-asynchronous-unwind-tables -fno-unwind-tables main_a64.c -o main_a64.o
```

Cross-check: `ld.lld -T simpleos_user_a64.ld -nostdlib -static --gc-sections
crt0_a64.o main_a64.o` reports `Machine: AArch64`, `Entry point address:
0x50000000`, `main` at `0x5000001c`, `base` at `0x50001000`.

## riscv64

- `simpleos_user_rv64.ld` — copy of the script written by
  `scripts/os/simpleos-sysroot-riscv64.shs` (`ENTRY(_start)`, text at
  `0x100000000`), with `INPUT($SYSROOT/lib/crt0.o)` pointed at `crt0_rv64.o`.
- `crt0_rv64.s`, `main_rv64.c` (same C as `main_x64.c`).

Produced with `Ubuntu clang version 18.1.3`, flags
`--target=riscv64-unknown-elf -march=rv64gc -mabi=lp64d -mcmodel=medany`
(main also `-O1 -ffreestanding -fno-pic -fno-stack-protector
-fno-asynchronous-unwind-tables -fno-unwind-tables`).

Cross-check from the repo root: `ld.lld -m elf64lriscv --no-relax -T
simpleos_user_rv64.ld -nostdlib -static --gc-sections main_rv64.o` reports
`Machine: RISC-V`, `Entry point address: 0x100000000`, `main` at
`0x100000018`, `base` at `0x100001000`.
