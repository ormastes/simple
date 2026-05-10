<!-- codex-design -->
# System Test Plan: portable_simd_fp_modules

## Coverage

- Generic x86_64 preset reports scalar FP and portable vector capability, but records that AVX lowering requires a runtime probe.
- RV64 Linux preset reports scalar FP through `F`/`D`, selects `riscv_fd`, and does not claim vector SIMD.
- Scalar-only selection on RV64 Linux still works when `vector_simd` is disabled.
- RV32 bare-metal integer-only preset does not claim scalar FP or vector SIMD and retains scalar fallback only.
- Unsupported vector requests emit explicit diagnostics.

## Acceptance Markers

- `name=linux-x86_64;scalar_fp=true;vector_simd=true`
- `runtime_probe=true`
- `modules=scalar_fp,vector_simd,scalar_fallback,x86_avx`
- `name=riscv64-linux;scalar_fp=true;vector_simd=false`
- `modules=scalar_fp,scalar_fallback,riscv_fd`
- `vector_simd_requested_but_target_lacks_vector_capability`
- `name=riscv32-baremetal;scalar_fp=false;vector_simd=false`
- `modules=scalar_fallback`
- `llvm-portable-numeric-ok`
- `native-portable-numeric-ok`

## Negative Markers

- silent vector support on RV64 `F`/`D`-only presets
- missing scalar fallback when target lowering is enabled
- generic x86_64 preset claiming AVX2 as unconditionally available
- LLVM x86_64 target config consuming AVX/AVX2 unconditionally without preserving the runtime-probe requirement
- native lowering claiming `riscv_v` behavior before scalable-vector MIR exists
