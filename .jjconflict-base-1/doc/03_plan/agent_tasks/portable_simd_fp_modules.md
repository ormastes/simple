<!-- codex-design -->
# Agent Tasks: portable_simd_fp_modules

## Current Status (2026-05-01)

- Startup/RSS evidence: PASS (`doc/09_report/verify/simd_startup_rss_evidence_2026-04-30.md`).
- Runtime perf evidence: superseded by Phase 1 (the 2026-04-30 WARN report measured the pre-intrinsic baseline; Wave 2 T1/T2 will re-measure with vectorized ChaCha20+SHA-256 against the same fixtures).
- FR `simd_int_intrinsics_for_crypto_2026-05-01` **Phase 1 LANDED** via Agent A (Wave 1, 2026-05-01): 10 bitwise/shift int intrinsics (xor / and / or / shl / shr × i32x4 + i32x8) implemented in `src/runtime/.../simd_int_ops.rs`, dispatched through the interpreter, spec-PASSed, and cross-referenced from the FR. Phase 2 (`Vec16u8` + AES-NI/PCLMUL one-shot block ops) and Phase 3 (`Vec2u64` + carry-less multiply for GHASH) remain **PROPOSED** — no agent assigned this wave.

### Wave 2 (in flight 2026-05-01 evening)

- **T1** vectorizing ChaCha20 quarter-round with Phase 1 ops — validates that the int intrinsics buy real perf in a pure-Simple AEAD.
- **T2** vectorizing SHA-256 message-schedule expansion (`σ0`/`σ1` over W[16..64]) with Phase 1 ops — validates the same for hashing.

These two are the empirical justification for unlocking Phase 2/3; if T1/T2 land measurable speedup against the 2026-04-30 baseline, that becomes the Phase-2 funding case.

#### Phase 1 dispatch gap (T1 found, T20 fixing 2026-05-01 evening)

T1 surfaced a pre-existing gap during ChaCha20 vectorization: `rt_simd_add_i32x4`, `rt_simd_sub_i32x4`, `rt_simd_mul_i32x4` and the i32x8 siblings are **declared as externs in `src/lib/.../simd.spl` but have no interpreter dispatch arm** in the runtime. T1 worked around this in the ChaCha20 vectorization with direct field arithmetic over the `Vec4i` fields. T20 is backfilling the missing dispatch arms in this same wave; until then, any consumer that calls `rt_simd_add_i32x4` etc. directly will trap on the FFI dispatcher.

#### Phase 1 perf evidence (already-validated via T1/T2)

- **T1 (ChaCha20)**: vertical 4-block SIMD layout achieves **1.7–1.8× over scalar** in interpreter mode for 256 B–1 KiB payloads (vertical = parallel independent message blocks across the lanes of the i32x4 register).
- **T2 (SHA-256 message schedule)**: horizontal layout (parallel lanes inside one block) is only **1–6 % slower than scalar** because σ0 is the only 4-wide-parallelizable subroutine in the schedule, and shuffle-equivalents must be emulated via field arithmetic without `Vec16u8` shuffle (Phase 2). **Implication**: prefer vertical layout for crypto streaming AEADs until Phase 2 lands.

See `doc/09_report/verify/wave_1to3_audit_2026-05-01.md` for the wave-level audit.

## Assumed Selection

Use Feature Option B and NFR Option B from the supplied plan.

## P0: Capability Registry

- Add a backend module that derives portable numeric capability facts from `TargetPreset`.
- Keep the surface architecture-neutral and family-oriented.
- Encode x86 runtime-probe requirements explicitly instead of assuming AVX from the generic preset.

## P0: Lowering Selection

- Add lowering-module selection for `scalar_fallback`, `x86_avx`, `riscv_fd`, and `riscv_v`.
- Ensure `scalar_fp`, `vector_simd`, and `target_lowering` are independently toggleable.
- Emit diagnostics when a requested family is unavailable.

## P1: Verification

- Add a compiled unit test that imports the real backend modules through `bin/simple run`.
- Cover x86_64, RV64 Linux, scalar-only RV64 Linux, and RV32 bare-metal integer-only cases.

## P2: Follow-On Work

- Integrate the registry into native and LLVM lowering entry points.
- Add scalable-vector MIR support before claiming RVV-native vector semantics.
