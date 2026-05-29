# Wave 1–5 Advisor Pivot Pattern Audit — 2026-05-01

Status: AUDIT (process evidence, cumulative across Waves 1–5)
Scope: 28 parallel Opus+advisor agents executed across compression / cipher / SIMD / TLS plan trees on 2026-05-01 (Waves 1–3 sweep + Wave 4 cleanup + Wave 5 ship).
Author: Wave-5 doc sweep, doc-only.

This report extends T25's `wave_1to3_audit_2026-05-01.md` (7-of-24 framings disproved) with the W4–W5 additions (T21 AES-256 runtime mutation, W5-D' B5b cherry-pick framing). Cumulative count: **9 of 28 (32 %)** bug-doc framings were disproved on contact. It also captures four reusable process patterns, a four-type advisor pivot taxonomy, and end-of-session lessons. Format mirrors the W1–W3 audit; rows 1–7 are inherited (re-stated for citability), rows 8–9 are W4–W5 additions.

Denominator note: "9 of 28" ≈ 32 % is computed against the cumulative count of *parallel agents that filed at least one bug-doc framing* across W1–W5 (28 agents). T25's W1–W3 fraction (7/24) used the same denominator definition. The headline is *framings disproved per filing-agent*, not per bug-doc — a single agent that filed multiple is counted once.

## Bug-doc framings disproved (cumulative 9 of 28)

| # | Agent | Wave | Bug-doc framing (claim) | Real root cause (verified) | Surfaced by |
|---|---|---|---|---|---|
| 1 | G | W1–W3 | `ed25519_rfc8032_vector_mismatch_2026-05-01` — byte-mismatch in `point_compress` (clamp/endian) | Constant-time scalar-mul leak on baremetal where externs were unwired; vector mismatch was a downstream symptom. Fix landed in `slskomnpwpsr fix(ed25519): constant-time scalar multiplication on secret path`; cross-link `oqpquwmyszmu`. | G + advisor reconcile |
| 2 | Q | W1–W3 | `aes128_gcm_stub_2026-05-01` — missing `rt_aes128_gcm_*` externs; later mis-restated as cross-module Result match dispatch | Externs existed but `text.from_char_code` lookup unwired across 9 callers; FFI dispatch table missing entries. Fixed by `yotnyuxtuoyw feat(interp): wire 4 AES externs into interpreter dispatch + FFI table`; closed FIXED in `qmooqrtsumru`. | Q empirical repro |
| 3 | T8 | W1–W3 | JWT REQ-006 / `interpreter_match_ok_arm_text_type_lookup_2026-05-01` — helper-fn match limitation in interpreter | Already fixed by Q's commit (extern wiring); the agent did not re-test against post-fix HEAD. Bug doc closed INVALID in `rszsowvlowpt`; regression-guarded by `oxumorrkmzqs`. | Advisor rerun on stale assumption |
| 4 | T16 | W1–W3 | `interpreter_u32_wrap_subtraction_2026-05-01` — u32 wraparound bug in LZMA range coder | Original framing partially right, but root cause is broader: no distinct `u32` type in interpreter — wraparound is simulated via i64 masking; this lane was symptom not blocker. Filed as known limitation, not LZMA-specific. | Cross-spec triage |
| 5 | T3 | W1–W3 | `aes128_gcm_decrypt_string_to_int_2026-05-01` — string→int parsing bug in decrypt path / `Err()` arm / CT compare | Leftover `_debug_bytes` scaffolding tripping a semantic check; no parse bug. Fix in `kwnportwwksr fix(aes-gcm): drop leftover _debug_bytes scaffolding`; FIXED in `rponkqvrvnvl`. | T3 + advisor on stale framing |
| 6 | T5 | W1–W3 | `hmac_sha512_pbkdf2_mismatch_2026-05-01` — HMAC-SHA-512 PBKDF2 algo mismatch | Bug-doc author paired `'passwd'` impl output against an RFC vector for `'password'` (off-by-one in test fixture, not impl). Industry vectors PASS in `zkxuxttwpzpw test(pbkdf2): RFC PBKDF2-HMAC-SHA-512 industry vectors`. | T5 + advisor refused fix-commit |
| 7 | T1 | W1–W3 | (Surfaced, not filed) ChaCha20 SIMD non-vectorization | `rt_simd_add_i32x4` declared extern in `simd.spl` but **no interpreter dispatch arm** (Phase 1 backfill gap). Worked around with field arithmetic; T20 backfilling. | T1 vectorization probe |
| 8 | T21 | W4 | AES-256 path inherits T3 "FIXED" from W1–W3 — assumed clean | T3's fix dropped `_debug_bytes` but did not address a separate runtime mutation propagation defect on AES-256 32-byte key expansion. Two independent bugs surfaced under one "FIXED" banner; T21 had to refile. | T21 empirical repro on AES-256 vectors |
| 9 | W5-D' | W5 | B5b retry framed as "pre-commit hook timeout blocking cherry-pick of jj-rebase patch" | Work was already on `main` under different SHAs (jj rebase had re-hashed parent chain); cherry-pick was failing because target commits were duplicates of HEAD content, not because of the hook. Pre-commit hook ran fine when invoked on a real diff. | Advisor reconcile against `git log -S` and `jj op log` |

## Process patterns (4)

### 1. Parallel-reconcile bundles when 5+ agents share file-cluster
**Symptom**: jj's auto-snapshot reconciles inflight working-copy edits into whichever change is currently active in the parallel-claude that next runs `jj describe`/`jj commit`. Title vs. tree-content drift is the norm; commit titles understate or misrepresent scope when ≥5 agents touch the same directory tree.
**Recovery**: `jj squash --from <bundled-change> --to <target>` extracts a single file to its proper home; titles remain misleading but tree contents become correct. Title rewrites are cosmetic and best deferred to a quiescent session.
**Applicability**: Any wave where 5+ agents share a file-cluster (e.g. `doc/02_requirements/feature/<topic>*`, `src/lib/crypto/*.spl`). Cap parallel agents at ≤5–6 per cluster.

### 2. `bin/simple test` (stale release) vs `bin/simple <spec>` (bootstrap binary) dispatch trap
**Symptom**: `bin/simple test` returns PASS while `bin/simple test/unit/.../<spec>.spl` returns FAIL on the same spec. Caused by release binary's `--mode=native` no-op-stub generation for unresolved std calls + `--mode=smf` swallowing runtime errors (per `feedback_compile_mode_false_greens.md`).
**Recovery**: Run target spec directly via `bin/simple test/path/spec.spl` (interpreter mode) before declaring PASS. Caught by advisor in T2 (sha256 parity), T3 (aes-gcm decrypt), T20 (simd dispatch).
**Applicability**: All wave audits, until R2-broader lands.

### 3. Advisor refused fabricated commits (3 confirmed this wave-set)
**Symptom**: Agent stages a commit claiming a feature/fix that primary-source evidence does not support. Confirmed cases: T11 AC-4 (claimed feature not present in tree), T5 fix-commit (claimed root-cause fix where impl was already correct), T24 PASS-flip (flipped a spec to PASS without addressing assertion).
**Recovery**: Advisor as final fabrication-gate before commit; agent re-routes to bug-doc filing or test-fixture correction. All 3 were rejected and re-routed.
**Applicability**: Any commit where the agent cannot produce a primary-source diff that matches the claim under prompted reconcile.

### 4. Vertical SIMD layout outperforms horizontal when shuffle/permute primitives are missing
**Symptom**: T1 ChaCha20 with vertical 4-block layout achieved 1.7–1.8× over scalar in interpreter mode (256 B–1 KiB payloads). T2 SHA-256 with horizontal layout was 1–6 % slower than scalar — only σ0 is 4-wide-parallelizable and shuffle must be emulated via field arithmetic.
**Recovery**: Prefer vertical layout (parallel independent blocks) over horizontal (parallel lanes inside one block) until Phase 2 (`Vec16u8` shuffle) lands.
**Applicability**: All SIMD vectorization work in Wave 6+ until shuffle/permute primitives ship.

## Advisor pivot taxonomy (4 types observed)

1. **Framing-correction** — advisor surfaces that the bug-doc's *cause* is wrong while the symptom is real. Examples: G (clamp→CT-leak), Q (extern→FFI-table), T3 (parse→debug-scaffolding), T5 (algo→fixture). 5 of 9 framings-disproved cases are this type.
2. **Scope-pull-back** — advisor flags that proposed change exceeds wave scope or pulls in unrelated diff. Examples: W5-A 5th-commit hold (caught wire-malformed CH2 routing through fallback before ship); T7 squash extraction.
3. **Fabricated-commit-refusal** — advisor refuses a commit whose tree does not match its claim. Examples: T11 AC-4, T5 fix-commit, T24 PASS-flip (3 confirmed).
4. **Hidden-bug-catch** — advisor surfaces a *separate* bug that the agent did not file because they assumed an upstream "FIXED" covered it. Examples: T21 AES-256 runtime mutation under T3's banner; T1 `rt_simd_add_i32x4` dispatch gap under Phase-1 closure.

## Lessons for next session (5)

1. **Empirical repro before trusting upstream framing.** Bug-doc "Proposed Fix Options" are author hypotheses. Each agent should run a minimal repro against current HEAD before committing to a framing — 5 of 9 disproved cases would have been caught at this gate (G, Q, T3, T5, T8).
2. **Pre-commit hook budget ≈ 2–3 min/commit; don't try to cherry-pick large jj-rebase synthetic patches.** W5-D' lost a session-hour to a cherry-pick that was duplicating HEAD content. When `jj op log` shows a recent rebase and `git log -S <unique-token>` finds the work already present, abort the cherry-pick — work is already shipped under different SHAs.
3. **Use `bin/simple <spec>` directly to bypass the stale-release dispatch.** `bin/simple test` aggregate runner can mask FAILs from `--mode=native`/`--mode=smf` no-ops. Direct interpreter-mode invocation is the only reliable PASS signal until R2-broader ships.
4. **Cap parallel agents at 5–6 per file-cluster.** Above 6, jj parallel-reconcile bundling becomes the dominant cost — recovery via `jj squash --from/--to` is per-file and serial. Prefer splitting agents across disjoint clusters even when the feature areas overlap.
5. **End-of-wave audit doc + advisor verification before declaring wave complete.** Both T25 (W1–W3) and this audit (W1–W5) caught durable bugs and fabrication patterns *after* per-agent self-reports said "done". Budget one orchestrator-led doc-only sweep per wave.

## Cross-references

- T25 W1–W3 audit: `doc/09_report/verify/wave_1to3_audit_2026-05-01.md` (rows 1–7 origin)
- Bug-doc fix hypothesis warning: user memory `feedback_bug_doc_fixes_are_guesses.md`
- Stale-release dispatch: user memory `feedback_compile_mode_false_greens.md`
- Parallel-reconcile clobbers: user memory `feedback_jj_uncommitted_clobbered_by_parallel.md`
- Advisor sub-agent access: user memory `feedback_subagent_advisor_access.md`
