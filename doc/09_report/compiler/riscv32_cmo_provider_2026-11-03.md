# RV32 CMO target-provider repair

Bug: `riscv32_cmo_uses_riscv64_only_provider_2026-08-26`.
Inspected base: `009546cbe28` (`release/1.0.0`).

The RV32 HAL imported the shared RISC-V CMO facade, which declared only
`rt_riscv64_*` symbols with `u64` address parameters. Its concrete foreign
provider existed only in the RV64 freestanding runtime. The RV32 HAL now
imports `os.kernel.arch.riscv32.cmo`, a Pure Simple instruction leaf with `u32`
register operands. The three range loops pass their existing `u32` addresses
directly. No foreign ABI, allocation, dispatch, or per-line capability lookup
was added. Existing boot/init policy and range behavior are unchanged.

## Bounded evidence

The installed default LLVM 23 excludes RISC-V targets. Ubuntu Clang 18.1.3 at
`/usr/bin/clang-18` provides RV32. Eight exact assembly templates were extracted
from the new source into LLVM IR: seven address operands are `i32`; every block
is side-effecting with a memory clobber. The compilation was:

```text
/usr/bin/clang-18 --target=riscv32-unknown-elf -march=rv32imac_zifencei -mabi=ilp32 -O2 -c -x ir actual-source-leaves.ll -o actual-source-leaves.o
```

`readelf` identifies ELF32 RISC-V. LLVM 18 disassembly contains all eight
expected instruction blocks, with address-bearing operations using `a0` and
each leaf returning. `llvm-nm -u` is empty. An additional assertion checks the
actual HAL import, removal of widening, all instruction blocks and unresolved
symbols. Artifacts: `/tmp/riscv32-cmo-evidence-20261103/`.

SHA-256:

- Clang: `6d99f6207153b8b2063ace5d2a6177debaf6a6b6f31649e03afac07b98ba0b4d`.
- Source leaf: `e80ce0ecc4a1e4b6c05d1a74b58488236dabc7a3b92daef61fd67060bbd9c29d`.
- HAL: `7681b69bb9ef5c4141e86765aa23aebf3fe4c442f61aa248d2fe6989ee39d7a9`.
- LLVM IR: `8ed5389dda70a7f63df4f498526f803f672bbdbe155f5949989bddd8acdbb117`.
- Object: `b8703ea5da66c175dd5b89491d45cf596ca964ee1eda33fac0356b12d1888276`.

The SFFI audit completed with source-only admission absent; direct-env working
guard passed. The structural SSpec is authored but UNRUN. This LLVM check
bypasses the Simple frontend: it is leaf encoding/XLEN evidence only. No Simple
native build, firmware/hardware execution, or Zifencei/Zicbom/Zicboz/Zicbop
capability admission is claimed. Assembler extension directives are not
runtime capability evidence. Interpreter-skipped assembly cannot qualify the
hardware path.
