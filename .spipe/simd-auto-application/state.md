# SStack State: simd-auto-application

## User Request
> next task from the plan — simd_auto_application (compiler infra, backend lowering, library adoption, matrix follow-up, verification)

## Task Type
feature

## Refined Goal
> Extend SIMD auto-application infrastructure: recipe metadata + legality scaffolding, vector width routing, fast_math restriction, multi-arch bitmanip lowering (x86/AArch64/RISC-V), crypto/compression SIMD adoption candidates, matrix dot/outer/matvec rewrites, and verification specs.

## Acceptance Criteria
- [x] AC-1: Recipe metadata extension — SIMD recipe entries with vector_width, legality_check, cost_model, fast_math_sensitive fields
- [x] AC-2: Vector width routing — shared capability helper that routes width (128/256/512/scalable) per target
- [x] AC-3: fast_math restriction — flag only enables reduction-order transforms, not precision-lossy rewrites
- [x] AC-4: x86 bitmanip lowering — portable intrinsics for popcnt, ctz, clz, bswap, bit_rotate
- [x] AC-5: AArch64 bitmanip lowering — same portable intrinsics mapped to ARM equivalents (RBIT, CLZ, REV)
- [x] AC-6: RISC-V bitmanip lowering — same portable intrinsics mapped to Zbb extension (cpop, ctz, clz, rev8, rol/ror)
- [x] AC-7: Crypto SIMD candidates — xor_block, rotate_block, clmul_pair identified with vectorization metadata
- [x] AC-8: Compression SIMD candidates — crc32_update, checksum_block, match_copy_run identified with vectorization metadata
- [x] AC-9: Matrix rewrites — dot_product, outer_product_update, matvec with profitability checks (break-even width)
- [x] AC-10: Verification specs — capability helpers + auto-vectorize matchers + bitmanip lowering tests

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-17
- [x] 6-refactor (Tech Lead) — 2026-05-17
- [x] 7-verify (QA) — 2026-05-17
- [x] 8-ship (Release Mgr) — 2026-05-17

## Phase Outputs

### 1-dev
10 ACs across 5 areas. 5 parallel agents (A-E). Existing: auto_vectorize*.spl (8 files in 60.mir_opt), runtime_simd_*.c (5 files), lint_simd.spl.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/compiler/60.mir_opt/mir_opt/simd_recipe_infra.spl (265 lines) — SimdRecipeEntry + SimdRecipeTable + VectorWidthRouter + FastMathPolicy + SimdAutoApplyContext
- src/compiler/60.mir_opt/mir_opt/bitmanip_lowering.spl (270 lines) — BitmanipOp + X86/Aarch64/Riscv lowering + dispatch
- src/compiler/60.mir_opt/mir_opt/simd_library_candidates.spl (249 lines) — SimdCandidate + Crypto/Compression candidates + VectorizationMetadata
- src/compiler/60.mir_opt/mir_opt/simd_matrix_rewrites.spl (248 lines) — MatrixOpProfile + DotProduct/OuterProduct/Matvec rewrites + engine
- test/unit/compiler/simd_auto_apply_spec.spl (~245 lines) — 20 tests
### 7-verify
20/20 tests PASS. Commit 03f8b1b1a5 pushed to origin/main.
