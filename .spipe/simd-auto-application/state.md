# SStack State: simd-auto-application

## User Request
> next task from the plan — simd_auto_application (compiler infra, backend lowering, library adoption, matrix follow-up, verification)

## Task Type
feature

## Refined Goal
> Extend SIMD auto-application infrastructure: recipe metadata + legality scaffolding, vector width routing, fast_math restriction, multi-arch bitmanip lowering (x86/AArch64/RISC-V), crypto/compression SIMD adoption candidates, matrix dot/outer/matvec rewrites, and verification specs.

## Acceptance Criteria
- [ ] AC-1: Recipe metadata extension — SIMD recipe entries with vector_width, legality_check, cost_model, fast_math_sensitive fields
- [ ] AC-2: Vector width routing — shared capability helper that routes width (128/256/512/scalable) per target
- [ ] AC-3: fast_math restriction — flag only enables reduction-order transforms, not precision-lossy rewrites
- [ ] AC-4: x86 bitmanip lowering — portable intrinsics for popcnt, ctz, clz, bswap, bit_rotate
- [ ] AC-5: AArch64 bitmanip lowering — same portable intrinsics mapped to ARM equivalents (RBIT, CLZ, REV)
- [ ] AC-6: RISC-V bitmanip lowering — same portable intrinsics mapped to Zbb extension (cpop, ctz, clz, rev8, rol/ror)
- [ ] AC-7: Crypto SIMD candidates — xor_block, rotate_block, clmul_pair identified with vectorization metadata
- [ ] AC-8: Compression SIMD candidates — crc32_update, checksum_block, match_copy_run identified with vectorization metadata
- [ ] AC-9: Matrix rewrites — dot_product, outer_product_update, matvec with profitability checks (break-even width)
- [ ] AC-10: Verification specs — capability helpers + auto-vectorize matchers + bitmanip lowering tests

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 5 areas. 5 parallel agents (A-E). Existing: auto_vectorize*.spl (8 files in 60.mir_opt), runtime_simd_*.c (5 files), lint_simd.spl.

### 5-implement
<pending>
