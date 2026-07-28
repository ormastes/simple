# CPU SIMD Engine2D Architecture Matrix Validator

This manual verifies REQ-007’s retained-evidence admission logic without
executing Simple, a native SIMD binary, a cross build, or QEMU.

## Scenario: validate and mutate one synthetic x86 receipt

1. Run the fixture with a 30-second hard bound (the executable SSpec enforces
   this with `process_run_timeout(..., 30000)`):

   ```sh
   sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs --self-test
   ```

2. Confirm the current synthetic receipt passes.
3. Confirm admission rejects a duplicate key, changed canonical-source bytes,
   changed compiler bytes, source/compiler symlinks, runtime-architecture and
   compiler-path mismatches, an emulated execution environment, an invalid x86
   feature, false executed or bit-exact flags, zero SIMD hits, scalar-oracle
   mismatch, and a forged receipt hash.
4. Confirm the final line is
   `cpu_simd_arch_matrix_self_test_status=pass`.

The fixture creates only bounded temporary source, executable, and evidence
files. Every case calls the same duplicate-safe parser, receipt calculator, and
`validate_retained_evidence` function used after a production evidence run.
Passing this fixture proves validator behavior only; it is not native SIMD
execution evidence and cannot promote ARM NEON or RISC-V RVV rows.
