# RV64 HAL cache transplant regression

The release transplant retained a spec that reads the result of
`hal_cache_init_with_isa`, but restored a void implementation. It also retained
calls to `_cache_range_end` and `riscv_noalloc_dtb_has_zicbom` without their
helper/import. The current boot-info caller initializes cache state from a
parsed DTB, so cache operations must read that same initialized state.

The repair returns the initialized snapshot, preserves parsed-DTB initialization,
restores checked range admission and non-wrapping cache iteration, and restores
bounded test-log counts for zero stride and very large ranges. Regression tests
cover the return value, range overflow, zero stride, empty ranges and saturation.

Diagnostic validation only (no Phase 2 rebuild or self-hosted certification):

- Runtime: `/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple`
- Environment: `SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpreter`
- Command suffix: `test <spec> --timeout=60 --format=text`
- `test/01_unit/os/kernel/arch/riscv/hal_cache_spec.spl`: 22/22 passed.
- `test/01_unit/os/kernel/arch/riscv64_boot_spec.spl`: 5/5 passed, including
  parsed-DTB capability and stride initialization.
- `test/01_unit/os/kernel/arch/riscv32_hal_io_event_parity_spec.spl`: 2/2 passed
  with `/opt/homebrew/opt/llvm/bin` prepended to PATH. The standalone C oracle
  emits the exact expected events and coverage (branches 4/4, MC/DC 2/2).

The initial RV32 parity failure was environment-sensitive: the default shell
PATH did not resolve llvm-profdata/llvm-cov. No RV32 behavior change is needed.
A separate diagnostic process capture probe returned its `hal-capture` stdout
and exit code 7 correctly. LLVM tooling must be present for the C oracle gate.
