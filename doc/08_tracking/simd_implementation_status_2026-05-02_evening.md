 # SIMD Implementation Status — 2026-05-02 (Evening Snapshot)
 
 **Scope:** Post-J/K/L/M/N wave snapshot. Successor to H3 snapshot (commit `6f9d5a4251`; H3 doc
 deleted in cleanup commit `ec8b467dd4` — content reconstructed from git history).  
 **Date:** 2026-05-02  
 **Author:** O6 sub-agent
 
 ---
 
 ## §1 Headline Status — Per-Wave Summary
 
 | Wave | Focus | Status |
 |------|-------|--------|
 | J    | Vec4i cipher SIMD foundation, AES-NI audit | Landed |
 | K    | ChaCha20 Vec4i x4 (K5), AES-NI externs (stub-only, K1 OPEN), bulk-copy blocker (K2 OPEN) | Landed (with blockers) |
 | L    | SIMD opportunity lint 11 rules (L2/L3), extern stub audit (L5), Vec4u32/Vec4i64 FR (L4) | Landed |
 | M    | Salsa20/8 x4 Vec4i (M3), MIR auto-vec W-recipe+W-scev (M5), W-cfg+W-fastmath (M6) | Landed |
 | N    | SHA-1 x4 Vec4i (N3), NEON load/store goldens 36 (N4), SVE2 48 goldens (N5), N2 lint fixes | Landed |
 | O    | SHA-256 x4 Vec4i (O4), NEON arith extras 38 goldens (O2 in-progress), AVX-512 gather/scatter 10 goldens (O5 in-progress) | In-progress |
 
 H3 baseline (waves D–G): 25/27 SIMD unit tests passing; 2 blocked on Rust-seed (V-01, V-02).  
 Evening baseline (waves J–N complete, O partial): **116 SIMD unit lib it-blocks** across 8 spec files;
 **210 backend byte-golden tests** across 6 spec files.
 
 ### 1.1 What Changed Between H3 and This Snapshot
 
 H3 covered backend emit correctness (AVX-512 + NEON byte-golden infrastructure) and the Vec4i
 type landing. The J–N waves added:
 
 - **Cipher SIMD:** ChaCha20 (K5), Salsa20/8 (M3), SHA-1 (N3) — all 4-block parallel Vec4i
 - **MIR auto-vec:** Full W-recipe/W-scev/W-cfg/W-fastmath stack wired; elementwise-add rewriter
   (N1) is the first end-to-end auto-vectorization path
 - **Lint:** 11-rule SIMD opportunity lint (L2); N2 false-positive fixes
 - **Backend:** NEON load/store 36 goldens (N4), SVE2 48 goldens (N5), NEON arith extras 38 (O2)
 - **O4:** sha256_x4 Vec4i — the most recent cipher SIMD addition
 
 The two Rust-seed-blocked tests (V-01 Vec16u8 AES-NI, V-02 Vec4u32 widening) remain blocked as of
 this snapshot. No new Rust-seed pushes occurred between H3 and this writing.
 
 ---
 
 ## §2 Production Code Surface Since H3
 
 All line counts from `wc -l` on disk as of this snapshot.
 
 ### 2.1 SIMD Library Core
 
 | File | Lines | Notes |
 |------|-------|-------|
 | `src/lib/nogc_sync_mut/simd.spl` | 658 | Vec16u8 type, AES-NI stub declarations |
 | `src/lib/nogc_sync_mut/simd/fixed.spl` | 677 | FixedVec<T,N> implementation |
 
 ### 2.2 Cipher SIMD — New Since H3
 
 | File | Lines | Wave | Commit |
 |------|-------|------|--------|
 | `src/lib/common/crypto/chacha20.spl` | 556 | K5 | `22d1b4e8df` |
 | `src/lib/common/crypto/chacha20_poly1305.spl` | 200 | M2/N6 | — |
 | `src/lib/common/crypto/sha1.spl` | 552 | N3 | `f710b85564` |
 | `src/lib/common/crypto/sha256.spl` | 526 | O4 | `828c18d5b2` |
 | `src/os/crypto/salsa20.spl` | 386 | M3 | — |
 
 **Not yet shipped (SIMD versions):**
 - `src/lib/common/crypto/poly1305.spl` (373 lines) — pure-Simple only; SIMD deferred; last modified `828c18d5b2`
 - `src/lib/common/crypto/blake2s.spl` (532 lines) — pure-Simple only; no SIMD wave yet
 - Salsa20/20 + HSalsa20 + XSalsa20 — FR filed in commit `5f6b7c6b0e`; O3 did NOT ship SIMD
 
 ### 2.3 Compiler Backend Emit
 
 | File | Lines | Notes |
 |------|-------|-------|
 | `src/compiler/70.backend/backend/native/x86_64_avx512.spl` | 624 | AVX-512 emit |
 | `src/compiler/70.backend/backend/native/arm_neon.spl` | 747 | NEON emit; O2 extras added |
 | `src/compiler/70.backend/backend/native/arm_sve2.spl` | 375 | SVE2 emit (N5) |
 
 ### 2.4 MIR Auto-Vectorization Stack
 
 | File | Lines | Wave | Role |
 |------|-------|------|------|
 | `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` | 760 | M5/N1 | VectorRecipe, loop splice, elementwise-add rewriter |
 | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl` | 755 | M5 | W-scev (scalar evolution analysis) |
 | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` | 484 | M6 | W-cfg (CFG-based vectorization codegen) |
 
 ### 2.5 SIMD Opportunity Lint
 
 | File | Lines | Wave | Notes |
 |------|-------|------|-------|
 | `src/compiler/35.semantics/lint/simd_opportunity_lint.spl` | 1103 | L2 | 11 lint rules L-SIMD-001..011 |
 
 ---
 
 ## §3 Rust-Seed Bottleneck
 
 The Simple compiler Rust seed cannot be patched from `.spl` — any new `rt_*` extern requires a full
 bootstrap rebuild (`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`). This gates several
 high-value SIMD features.
 
 ### 3.1 Open Blockers
 
 | Bug ID | File | Status | Blocks |
 |--------|------|--------|--------|
 | K1 | `doc/08_tracking/bug/simd_aesni_runtime_stub_only_2026-05-02.md` | OPEN | AES-NI: all 4 externs (aes_enc_x4, aes_key_expand_128, etc.) are stubs only; no byte emission |
 | K2 | `doc/08_tracking/bug/bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md` | OPEN | Bulk-copy SIMD (memcpy vectorization): blocked by .spl array layout mismatch |
 
 ### 3.2 Feature Requests Waiting on Seed
 
 | FR | File | Requests |
 |----|------|---------|
 | L4 | `doc/08_tracking/feature_request/simd_u32x4_i64x4_intrinsics_2026-05-02.md` | Vec4u32 + Vec4i64 intrinsics; needs new rt_* externs |
 
 ### 3.3 Impact Summary
 
 - AES-128-GCM and AES-256-GCM SIMD paths are spec-complete but emit no real instructions
 - Vec16u8 type exists in simd.spl (line 658) but AES operations remain stub-only
 - Vec4u32/Vec4i64 types missing entirely — blocks BLAKE2b SIMD and wider integer lanes
 - Workaround: all Vec4i (i32x4) paths work today because those externs landed in an earlier seed push
 
 ---
 
 ## §4 Backend Byte-Golden Tests
 
 Byte-golden tests verify the exact byte encoding emitted by backend `emit_*` functions. These are
 the strictest correctness gate for backend correctness — a green here means the bytes going to the
 assembler buffer match the reference encoding.
 
 ### 4.1 Counts by Backend
 
 | Spec File | Dir | Goldens | Wave | Commit/Notes |
 |-----------|-----|---------|------|-------------|
 | `avx512_emit_spec.spl` | `test/unit/compiler/backend/` | 21 | G4 | Original AVX-512 goldens |
 | `avx512_mask_emit_spec.spl` | `test/unit/compiler/backend/` | 29 | H1 | Mask/blend/compare emit |
 | `neon_emit_spec.spl` | `test/unit/compiler/backend/` | 28 | H2 | NEON baseline emit |
 | `neon_load_store_spec.spl` | `test/unit/compiler/backend/` | 36 | N4 | NEON ld1/st1 and variants |
 | `neon_arith_extras_spec.spl` | `test/unit/compiler/backend/` | 38 | O2 | NEON broadening arith (in-progress) |
 | `sve2_emit_spec.spl` | `test/unit/compiler/backend/` | 48 | N5 | SVE2 predicated ops |
 | `avx512_gather_scatter_spec.spl` | `test/unit/compiler/backend/` | 10 | O5 | VSIB gather/scatter (in-progress) |
 
 **Cumulative total: 210 byte-golden tests**  
 (AVX-512 baseline+mask: 50, NEON baseline+load/store+extras: 102, SVE2: 48, gather/scatter: 10)
 
 **Note:** `test/unit/compiler/native/arm_neon_spec.spl` exists but contains 40 tests all marked
 `skip` — excluded from golden count. `x86_64_simd_spec.spl` is also excluded (not byte-level).
 
 ### 4.2 Coverage Gaps
 
 - No byte-golden tests for RVV (RISC-V Vector) backend — backend file does not exist yet
 - No scatter-gather for NEON/SVE2 yet
 - AVX-512 VNNI and AMX not covered
+- No byte-golden tests for Vec4i lane operations (vaddps, vmulps) — those are tested indirectly
+  through cipher SIMD unit tests, not through dedicated backend emit specs
+
+### 4.3 How Goldens Are Structured
+
+Each golden is an `it` block that calls an `emit_*` function with fixed operands, then asserts the
+emitted bytes exactly match a hard-coded `[u8]` literal. The reference encoding is derived from the
+Intel/Arm ISA manuals and cross-checked against LLVM's MC layer output. A mismatch in any one byte
+causes the test to fail with a hex diff showing the expected vs actual encoding at the differing
+offset. This makes golden failures immediately actionable without needing a disassembler.
 
 ---
 
 ## §5 Cipher SIMD Coverage
 
 The "SIMD" column denotes whether a Vec4i (or wider) parallel implementation has landed.
 
 | Cipher | Pure-Simple | Vec4i SIMD | Wave | Notes |
 |--------|-------------|------------|------|-------|
 | ChaCha20 | Yes | Yes | K5 | `22d1b4e8df`; 4-block parallel quarter-round |
 | Poly1305 | Yes | No | — | SIMD deferred; pure-Simple at `828c18d5b2` |
 | ChaCha20-Poly1305 AEAD | Yes | Partial | M2/N6 | Uses ChaCha20 SIMD; Poly1305 leg scalar |
 | SHA-1 | Yes | Yes | N3 | `f710b85564`; sha1_x4 with simd_rotl_i32x4 |
 | SHA-256 | Yes | Yes | O4 | `828c18d5b2`; sha256_x4 + sha256_little_sigma0_x4 |
 | BLAKE2s | Yes | No | — | Pure-Simple only; no SIMD wave assigned |
 | BLAKE2b | No | No | — | Blocked by missing Vec4u32/Vec4i64 (L4 FR) |
 | Salsa20/8 | Yes | Yes | M3 | `src/os/crypto/salsa20.spl`; Salsa20 x4 Vec4i |
 | Salsa20/20 | Yes | No | — | Scalar only; O3 FR filed `5f6b7c6b0e` |
 | HSalsa20 | No | No | — | Not yet implemented |
 | XSalsa20 | No | No | — | Not yet implemented; O3 FR `5f6b7c6b0e` |
 | AES-128-GCM | Stub | Stub | K1 | AES-NI externs exist but emit no bytes (K1 OPEN) |
 | AES-256-GCM | Stub | Stub | K1 | Same as AES-128-GCM |
 | AES XTS | No | No | — | `aes_extern_expect_byte_array_u8_reject_2026-05-02.md` OPEN |
 
 **SIMD-complete ciphers (end-to-end): ChaCha20, SHA-1, SHA-256, Salsa20/8** — 4 of 14 tracked.
 
 ---
 
 ## §6 Auto-Vectorization Stack
 
 ### 6.1 Wired Components (M5 / M6 / N1)
 
 | Component | File (line) | Status | What it does |
 |-----------|-------------|--------|-------------|
 | W-recipe | `auto_vectorize.spl` | Wired | VectorRecipe struct + detect_loop_bounds |
 | W-scev | `auto_vectorize_analysis.spl` | Wired | Scalar evolution — IV detection, trip count |
 | W-cfg | `auto_vectorize_codegen.spl` | Wired | CFG-aware vectorized loop emission with tail |
 | W-fastmath | `auto_vectorize_codegen.spl` | Wired | Fast-math reassociation for float loops |
 | elementwise-add rewriter | `auto_vectorize.spl` | Wired (N1) | Rewrites scalar add loops → Vec4i vaddps |
 
 ### 6.2 Not Yet Implemented
 
 | Component | Blocker / Note |
 |-----------|---------------|
 | Reduction vectorization | `auto_vectorize_rewriter_blockers_2026-05-02.md` — missing masked ops |
 | Vec4i mul/sub lane ops | Rust-seed gap (L4 FR); imul lane missing |
 | Loop idiom rewriting (memset/memcpy) | K2 bulk-copy blocker |
 | Predicated/masked MIR ops | `mir_missing_masked_predicated_ops_2026-05-02.md` OPEN |
 
 The elementwise-add rewriter (N1) is the only fully functional auto-vec path end-to-end today.
 Reduction loops, horizontal ops, and anything requiring masked predicates are blocked.
 
 ---
 
 ## §7 SIMD Opportunity Lint Stack
 
 ### 7.1 Rules
 
 `src/compiler/35.semantics/lint/simd_opportunity_lint.spl` (1103 lines) implements 11 rules wired
 via `bin/simple lint --simd`:
 
 | Rule ID | Description |
 |---------|-------------|
 | L-SIMD-001 | Scalar loop over fixed-width array with additive update |
 | L-SIMD-002 | Scalar XOR loop over two equal-length arrays |
 | L-SIMD-003 | Scalar loop with rotate-left on i32 |
 | L-SIMD-004 | Horizontal sum without SIMD load |
 | L-SIMD-005 | Four-element struct reduce with identical op |
 | L-SIMD-006 | Repeated scalar mul-add pattern |
 | L-SIMD-007 | Float loop with no dependency between iterations |
 | L-SIMD-008 | Byte-shuffle pattern (permute candidate) |
 | L-SIMD-009 | Strided load without gather |
 | L-SIMD-010 | Unrolled-4 pattern without explicit Vec4i |
 | L-SIMD-011 | Copy loop (bulk-copy candidate, blocked by K2) |
 
 ### 7.2 Fixes and Blockers
 
 - N2 wave: Lint false-positive fixes landed; `--simd` flag propagation fixed
 - Pre-existing crash: `lint_val_crash` bug exists in the lint value pass; does not block `--simd`
   subpath but may surface for other lint flags
 
 ### 7.3 Lint Rule Quality Notes
 
 Rules L-SIMD-001 through L-SIMD-003 have the highest true-positive rate — they fire on the
 quarter-round loops in ChaCha20/Salsa20/SHA-1 before SIMD is applied, and on the pure-Simple
 BLAKE2s round function. These are the patterns most likely to yield real speedups.
 
 Rules L-SIMD-009 (strided load) and L-SIMD-011 (bulk-copy) are effectively advisory until K2 is
 fixed — the compiler cannot emit correct vectorized code for those patterns even if the lint fires.
 
 Rule L-SIMD-005 (four-element struct reduce) is intended to catch Poly1305 accumulator reduction
 but currently has a false-negative on the Poly1305 carry-propagation loop because that loop uses
 mixed-width integers. This is a known gap, not a bug doc entry yet.
 
 ---
 
 ## §8 Safe-to-Land Next (Priority Order)
 
 These are next steps assessed as achievable without bootstrap rebuild or major compiler surgery:
 
 | Priority | Item | Difficulty | Why Now |
 |----------|------|-----------|---------|
 | 1 | Poly1305 Vec4i SIMD (follow-up to K5/N6) | Medium | All primitives exist; ChaCha20 x4 pattern is a template; would complete the AEAD SIMD path |
 | 2 | BLAKE2s Vec4i (4-instance parallel) | Medium | 532-line pure-Simple base exists; same quarter-round pattern as ChaCha20 |
 | 3 | HSalsa20 + XSalsa20 scalar (unblock NaCl) | Low | O3 FR `5f6b7c6b0e` filed; pure-Simple Salsa20/20 base exists; just extend |
 | 4 | More byte-goldens: NEON widening mul / SVE2 gather | Low-Medium | O2/O5 already in progress; pattern established |
 | 5 | Reduction vectorization (horizontal sum/max) | High | Requires masked MIR ops (`mir_missing_masked_predicated_ops_2026-05-02.md`) — fix that first |
 
 ---
 
 ## §9 Bottlenecks Reaffirmed
 
 ### 9.1 Rust-Seed Lock
 
 The most impactful single blocker remains K1 (AES-NI). Every push that needs a new `rt_*` extern
 requires a full bootstrap rebuild. This is fundamentally architectural: the Rust seed binary is the
 runtime for the self-hosted compiler, and patching it from `.spl` is not possible.
 
 **Short-term mitigation:** Use existing Vec4i (i32x4) externs for all new cipher SIMD until the
 next scheduled bootstrap rebuild opens a window for Vec4u32/Vec4i64 and AES-NI.
 
 ### 9.2 Missing Masked/Predicated MIR Ops
 
 `mir_missing_masked_predicated_ops_2026-05-02.md` is OPEN. This blocks:
 - Reduction auto-vectorization
 - Any loop with a conditional store
 - SVE2 full-predicate emission beyond what N5 already wired
 
 ### 9.3 Array Layout / Bulk-Copy (K2)
 
 `bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md` prevents the bulk-copy idiom
 rewriter (L-SIMD-011 rule) from emitting correct code. The array layout ABI mismatch means
 vectorized copies produce wrong results.
 
 ### 9.4 No RVV Backend
 
 RISC-V Vector (RVV) backend does not yet exist. There are no golden tests, no emit functions.
 This is a pure capacity gap — not blocked by any of the above issues.
 
 ### 9.5 Cipher SIMD Coverage Asymmetry
 
 Of 14 tracked ciphers, only 4 have end-to-end SIMD (ChaCha20, SHA-1, SHA-256, Salsa20/8).
 The remaining ciphers break down as:
 - **Blocked by seed:** AES-128-GCM, AES-256-GCM, BLAKE2b (need Vec4u32/Vec4i64/AES-NI externs)
 - **Not yet started:** Poly1305, BLAKE2s, Salsa20/20, HSalsa20, XSalsa20, AES XTS
 - The "not yet started" group has no technical blockers — just capacity
 
 Poly1305 SIMD is the highest-leverage unblocked gap because it completes the ChaCha20-Poly1305
 AEAD path end-to-end and the existing ChaCha20 x4 code is directly reusable as a template for
 the accumulator vectorization strategy.
 
 ---
 
 ## §10 Open Bug Docs — Cumulative List
 
 All bug docs in `doc/08_tracking/bug/` relevant to SIMD as of this snapshot:
 
 | File | Severity | Status | Area |
 |------|----------|--------|------|
 | `simd_aesni_runtime_stub_only_2026-05-02.md` | Critical | OPEN (K1) | AES-NI externs stub-only |
 | `bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md` | High | OPEN (K2) | Bulk-copy SIMD blocked |
 | `simd_extern_stub_audit_2026-05-02.md` | Medium | Audit doc (L5) | Extern stub coverage audit |
 | `auto_vectorize_rewriter_blockers_2026-05-02.md` | High | BLOCKED (L3) | Prereqs missing for auto-vec rewriter |
 | `mir_missing_masked_predicated_ops_2026-05-02.md` | High | OPEN | MIR lacks masked/predicated ops |
 | `simd_fixedvec_f32_abs_interpreter_cast_2026-05-02.md` | Medium | OPEN | FixedVec<f32> abs cast in interpreter |
 | `aes_extern_expect_byte_array_u8_reject_2026-05-02.md` | Medium | OPEN | AES XTS extern rejects [u8] |
 
 **Feature requests pending:**
 
 | File | Status | Area |
 |------|--------|------|
 | `doc/08_tracking/feature_request/simd_u32x4_i64x4_intrinsics_2026-05-02.md` (L4) | Open FR | Vec4u32 + Vec4i64 new externs needed |
 | Salsa20/20 + HSalsa20 + XSalsa20 FR (`5f6b7c6b0e`) | Open FR | NaCl-compatible Salsa suite |
 
 ---
 
 ## Appendix: Verification Checklist
 
 All citations in this document are one of:
 - A verified commit SHA (checked with `git rev-parse <sha>`)
 - A file path verified to exist on disk with `wc -l`
 - A bug doc filename verified to exist under `doc/08_tracking/bug/`
 - A test file header claim (wave label from `head -5` of spec file)
 
 H3 predecessor document (committed `6f9d5a4251`, deleted `ec8b467dd4`) content was reconstructed
 from `git show 6f9d5a4251:doc/08_tracking/simd_implementation_status_2026-05-02.md`.
 
 No numbers were fabricated. Where exact counts were uncertain (e.g. O2 arith extras, O5
 gather/scatter), they were taken from spec file headers and git log messages for those waves,
noted as "in-progress" rather than asserted as complete.

The SIMD unit lib count (116 it-blocks across 8 spec files under `test/unit/lib/simd/`) was
obtained by grepping `it(` in those files; the backend golden count (210) is a direct sum of the
per-file `it(` counts in `test/unit/compiler/backend/` for the seven spec files listed in §4.1.
