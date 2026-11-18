# RV32 static linker fixtures

Produced on WSL Ubuntu 24.04 with clang/LLD 18 (RV32IMAC, ILP32 soft-float).
`.option norelax` keeps R_RISCV_RELAX/ALIGN out (RV32 ALIGN fails closed).

```sh
clang --target=riscv32-unknown-elf -march=rv32imac -mabi=ilp32 -c start.s -o start.o
clang --target=riscv32-unknown-elf -march=rv32imac -mabi=ilp32 -c provider.s -o provider.o
ld.lld --no-relax -static -e _start -Ttext=0x80200000 start.o provider.o -o oracle.elf
```

`start.o` carries twelve relocations: PCREL_HI20 (2), PCREL_LO12_I,
PCREL_LO12_S, HI20 (2), LO12_I, LO12_S, CALL_PLT, BRANCH, JAL and one
R_RISCV_32 data word (`data_ptr`). The trailing `lui %hi(data_ptr)` keeps
`.data` of start.o live under the driver's default section GC.

LLD oracle (`-Ttext=0x80200000`): `_start=0x80200000`, `data_ptr=0x8020104c`
holding `data_value=0x80201050`. The spec checks the same
relations layout-relatively against the Simple linker's image.
Generator: `C:/dev/wt/xc-wsl-scripts/sbm-rv32_fix.sh` (lane script, not tracked).
