# CPU SIMD Engine2D Arch Matrix

- cpu_simd_engine2d_arch_matrix_host_arch=x86_64
- cpu_simd_engine2d_arch_matrix_strict=0
- cpu_simd_engine2d_arch_matrix_target_build=1
- cpu_simd_engine2d_arch_matrix_native_build_simple=src/compiler_rust/target/debug/simple
- cpu_simd_engine2d_arch_matrix_source_contract_status=pass
- cpu_simd_engine2d_arch_matrix_source_contract_reason=mutable-aarch64-dispatch-present
- cpu_simd_engine2d_arch_matrix_x86_64_status=skip
- cpu_simd_engine2d_arch_matrix_x86_64_reason=engine2d-simd-externs-not-in-binary-bootstrap-required
- cpu_simd_engine2d_arch_matrix_x86_64_simple_bin=bin/simple
- cpu_simd_engine2d_arch_matrix_x86_64_report=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/x86_64/report.md
- cpu_simd_engine2d_arch_matrix_aarch64_status=unavailable
- cpu_simd_engine2d_arch_matrix_aarch64_reason=missing-simple-bin
- cpu_simd_engine2d_arch_matrix_aarch64_simple_bin=
- cpu_simd_engine2d_arch_matrix_aarch64_report=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/aarch64/report.md
- cpu_simd_engine2d_arch_matrix_riscv64_status=unavailable
- cpu_simd_engine2d_arch_matrix_riscv64_reason=missing-simple-bin
- cpu_simd_engine2d_arch_matrix_riscv64_simple_bin=
- cpu_simd_engine2d_arch_matrix_riscv64_report=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/riscv64/report.md
- cpu_simd_engine2d_arch_matrix_x86_64_runtime_compile_status=pass
- cpu_simd_engine2d_arch_matrix_x86_64_runtime_compile_reason=compiled
- cpu_simd_engine2d_arch_matrix_x86_64_runtime_compile_cc=cc
- cpu_simd_engine2d_arch_matrix_x86_64_runtime_compile_flags=
- cpu_simd_engine2d_arch_matrix_aarch64_runtime_compile_status=pass
- cpu_simd_engine2d_arch_matrix_aarch64_runtime_compile_reason=compiled
- cpu_simd_engine2d_arch_matrix_aarch64_runtime_compile_cc=aarch64-linux-gnu-gcc
- cpu_simd_engine2d_arch_matrix_aarch64_runtime_compile_flags=
- cpu_simd_engine2d_arch_matrix_riscv64_runtime_compile_status=pass
- cpu_simd_engine2d_arch_matrix_riscv64_runtime_compile_reason=compiled
- cpu_simd_engine2d_arch_matrix_riscv64_runtime_compile_cc=riscv64-linux-gnu-gcc
- cpu_simd_engine2d_arch_matrix_riscv64_runtime_compile_flags=
- cpu_simd_engine2d_arch_matrix_riscv64_rvv_runtime_compile_status=pass
- cpu_simd_engine2d_arch_matrix_riscv64_rvv_runtime_compile_reason=compiled
- cpu_simd_engine2d_arch_matrix_riscv64_rvv_runtime_compile_cc=riscv64-linux-gnu-gcc
- cpu_simd_engine2d_arch_matrix_riscv64_rvv_runtime_compile_flags=-march=rv64gcv -mabi=lp64d
- cpu_simd_engine2d_arch_matrix_x86_64_target_binary_status=pass
- cpu_simd_engine2d_arch_matrix_x86_64_target_binary_reason=engine2d-simd-c-kernels-ran
- cpu_simd_engine2d_arch_matrix_x86_64_target_binary_triple=x86_64-unknown-linux-gnu
- cpu_simd_engine2d_arch_matrix_x86_64_target_binary_path=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/x86_64/engine2d-simd-c-kernels/engine2d_simd_c_test
- cpu_simd_engine2d_arch_matrix_aarch64_target_binary_status=pass
- cpu_simd_engine2d_arch_matrix_aarch64_target_binary_reason=engine2d-simd-c-kernels-ran
- cpu_simd_engine2d_arch_matrix_aarch64_target_binary_triple=aarch64-unknown-linux-gnu
- cpu_simd_engine2d_arch_matrix_aarch64_target_binary_path=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/aarch64/engine2d-simd-c-kernels/engine2d_simd_c_test
- cpu_simd_engine2d_arch_matrix_riscv64_target_binary_status=pass
- cpu_simd_engine2d_arch_matrix_riscv64_target_binary_reason=engine2d-simd-c-kernels-ran
- cpu_simd_engine2d_arch_matrix_riscv64_target_binary_triple=riscv64gc-unknown-linux-gnu
- cpu_simd_engine2d_arch_matrix_riscv64_target_binary_path=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/riscv64/engine2d-simd-c-kernels/engine2d_simd_c_test
- cpu_simd_engine2d_arch_matrix_passed_count=0
- cpu_simd_engine2d_arch_matrix_unavailable_count=3
- cpu_simd_engine2d_arch_matrix_failed_count=0
- cpu_simd_engine2d_arch_matrix_runtime_compile_unavailable_count=0
- cpu_simd_engine2d_arch_matrix_runtime_compile_failed_count=0
- cpu_simd_engine2d_arch_matrix_target_binary_unavailable_count=0
- cpu_simd_engine2d_arch_matrix_target_binary_failed_count=0
- cpu_simd_engine2d_arch_matrix_status=pass
- cpu_simd_engine2d_arch_matrix_reason=target-binary-builds-pass

## Hosted Simple Binary Proof (2026-07-10)

- x86_64 LLVM native binary: build pass, exact row probe exit `0`.
- AArch64 LLVM hosted binary: `ELF 64-bit ARM aarch64`, QEMU user-mode exit `0`.
- RV64GC LLVM hosted binary: `ELF 64-bit RISC-V, RVC, double-float ABI`, QEMU
  user-mode exit `0`.
- All three binaries call the public `engine2d_simd_fill_row_u32` Simple wrapper
  and validate row length plus exact `0xFF010203` pixel data.
- RVV opt-in hosted binary: vector-enabled QEMU exit `0` after exact fill/copy
  checks and at least two native SIMD hits. Disassembly contains `vsetvli`,
  `vmv.v.x`, `vle64.v`, and `vse64.v`.
