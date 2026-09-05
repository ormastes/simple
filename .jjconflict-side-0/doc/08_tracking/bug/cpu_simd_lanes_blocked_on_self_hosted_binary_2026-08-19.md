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

## Update 2026-08-19 (render-harden SIMD lane sweep)
- `simd_parity_spec.spl` now 37/37 under ALL six `SIMPLE_2D_SIMD` values
  (off/sse2/avx2/neon/rvv/auto) — 6 new gate examples added (ArmSimdGate NEON
  baseline, RiscvSimdGate rvv opt-in token).
- Forced-foreign-ISA honesty fixed in `simd_kernels.spl`:
  `SIMPLE_2D_SIMD=neon|rvv` on x86 previously reported `arm_available=true` /
  `riscv_available=true` with no disclosure. Now `host_simd_level()` probes the
  REAL host, `*_available` reflect the host, `reason` carries an explicit
  `DISCLOSURE: ... forced ISA did NOT run`, and
  `cpu_simd_required_evidence_valid` fails closed on a forced arch not backed
  by the host.
- `check-cpu-simd-engine2d-arch-matrix.shs` with
  `CPU_SIMD_ARCH_MATRIX_TARGET_BUILD=1`: all 4 runtime cross-compiles PASS
  (incl. riscv64 `-march=rv64gcv`), and all 3 target C-kernel binaries BUILD
  AND RUN green under qemu-user (x86_64 native, qemu-aarch64,
  qemu-riscv64 `-cpu rv64,v=true,vlen=128`). Only the per-arch *Simple-binary*
  evidence stays red (`simple-bin-forbidden` / `missing-simple-bin`) — blocked
  on the self-hosted redeploy above, plus missing aarch64/riscv64 self-hosted
  `simple` binaries (no prebuilt artifacts in-tree).
- `check-simpleos-qemu-engine2d-simd-kernels.shs` PASS (ARM64 NEON + x86_64
  SSE2 fill kernels + receipt symbols).
- NEW environmental gap: `check-llvm-simd-row-native-arch.shs` fails
  fast with `missing-arm-linux-gnueabihf-readelf` — host lacks armhf binutils
  (`apt install binutils-arm-linux-gnueabihf` would unblock; aarch64/riscv64
  toolchains and qemu are present).
