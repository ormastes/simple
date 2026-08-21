# LLVM SIMD row array ABI

Mirror of `test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl`.

The executable SSpec checks packed pixel rows use the runtime array ABI, the Simple wrapper remains narrow and typed, hosted cross compilers do not enter the SimpleOS RV64 lane, and each hosted architecture has an exact native-hit probe.

The checks are static contract assertions rather than an end-to-end SIMD execution benchmark.
