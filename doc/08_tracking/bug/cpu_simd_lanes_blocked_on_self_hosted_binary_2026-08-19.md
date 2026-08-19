# CPU-SIMD evidence lanes blocked: refuse Rust seed, no self-hosted bin/simple deployable

- **Date:** 2026-08-19
- **Status:** OPEN (blocked-by: bootstrap redeploy — see stage3 SEGV bug)
- **Severity:** medium — two evidence lanes red for environmental reasons, kernels themselves proven green by sibling lanes

## Symptom
- `check-cpu-simd-engine2d-evidence.shs` → `cpu_simd_evidence_status=fail
  cpu_simd_evidence_reason=simple-bin-forbidden`
  (`simple_bin_source=missing-self-hosted-engine2d-simd-rust-seed-forbidden`)
- `check-cpu-simd-engine2d-arch-matrix.shs` → x86_64 arm fails for the same
  `simple-bin-forbidden` reason (aarch64/riscv64 report `disabled`, runtime
  cross-compiles green), so
  `cpu_simd_engine2d_arch_matrix_reason=arch-evidence-failed`.

Both lanes correctly enforce the "default tooling = pure-Simple self-hosted
binary" rule and refuse the Rust seed. `bin/simple` is currently the seed, and
all four tracked stage binaries SEGV
(`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`),
so no compliant binary exists to run them with.

## Not a kernel regression
Same sweep, same host: `check-engine2d-simd-c-kernels.shs` PASS
(fill 8k parallel 29.5ms, row scheduling true), `check-engine2d-simd-8k-ops.shs`
PASS, and `test/02_integration/rendering/simd_parity_spec.spl` is 31/31 under
both `SIMPLE_2D_SIMD=auto` and `SIMPLE_2D_SIMD=off` (scalar lane).

## Resolution path
Unblocks automatically once a working self-hosted `bin/simple` is redeployed;
no lane-side fix is appropriate (weakening the forbidden-seed check would be
fail-open).
