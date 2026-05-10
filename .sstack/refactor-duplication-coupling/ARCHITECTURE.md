# Refactor Architecture — refactor-duplication-coupling

**Date:** 2026-04-27
**Phase:** 3-arch
**Scope:** All 127 line-mode duplicate groups in `src/compiler/` above `--min-impact 50`.

## Refactor pattern catalog

The 127 findings collapse into 5 patterns. Each has a standard treatment.

### Pattern A — Sibling-file shared loop (CLUSTER)
**Signature:** Multiple files in the same directory share an identical multi-line loop body (typically docstring/comment skipping in linters, or token-class branching in parsers).
**Treatment:** Extract a single helper into a sibling `_<dir>_common.spl` (or existing `__init__.spl`) and replace every occurrence with a call.
**Risk:** Low. Loop bodies are usually behaviorally identical; verify with side-by-side diff.
**Affected files (line-mode):** all of `src/compiler/35.semantics/lint/*` (≈10 files share docstring-skip)

### Pattern B — Sibling-file branch ladder
**Signature:** Files in the same backend layer share `if-elif` ladders that map a type/opcode to a representation.
**Treatment:** Extract a `match_<thing>(x) -> Result<...>` helper. If pattern is large, consider a small lookup table.
**Risk:** Medium. Ladder ordering may matter; preserve first-match semantics.
**Affected files:** `70.backend/backend/cranelift_type_mapper.spl + common/type_mapper.spl`, `70.backend/backend/{c_codegen_adapter,llvm_type_mapper,llvm_cross_target}.spl` (per existing finding list).

### Pattern C — Within-file repeated block
**Signature:** A file repeats the same 5–8-line block multiple times within itself (often inside the same function or sibling functions).
**Treatment:** Extract a private (file-local) helper. No new public API.
**Risk:** Low. Pure local refactor.
**Affected files:** `vhdl_backend.spl`, `shb_reader.spl`, `fix/main.spl`, `type_layout.spl`, `monomorphize/deferred_deserialize.spl`, `driver_public_api.spl`, several lint files have intra-file dups in addition to cross-file.

### Pattern D — Cross-layer copy-paste
**Signature:** The same logic appears in two layers (e.g. backend type-mapping echoed in tooling like `ffi_gen/type_mapping.spl`).
**Treatment:** Identify the canonical location (usually the lower layer). Move the logic there as a public helper, import from the higher layer.
**Risk:** **Medium-high.** Crosses MDSOC layer boundaries — verify import direction (lower → higher) is preserved. Sometimes the right answer is to keep the duplication if layers should not couple, in which case file as a closed "design intent" item.
**Affected files:** `70.backend/.../type_mapper.spl` ↔ `90.tools/ffi_gen/type_mapping.spl`, possibly `linker_wrapper.spl` ↔ `linker_wrapper_lib_support.spl`, `obj_taker.spl`.

### Pattern E — Parameter-list repetition (3+ args)
**Signature:** Same multi-arg function signature repeats 3+ times.
**Treatment:** Introduce a parameter object (struct) that bundles the args.
**Risk:** Low if the args are always passed together; medium if call sites pass subsets.
**Detection:** Not surfaced by `duplicate-check` directly; will spot-check during Pattern B/D refactors.

## Batch index — ordered by ROI (impact / files-touched)

Each batch is ≤5 files and produces one commit. Order respects MDSOC layers (lower → higher) where possible to minimize re-work.

| # | Batch | Pattern | Files | Groups | Impact gain |
|---|-------|---------|-------|--------|------------|
| 1 | **35.semantics/lint docstring-skip helper (part 1)** | A | `_lint_common.spl` (new) + 4 lint files (mcp_perf_lint, remote_exec_lint, security_hardcoded_secret, security_insecure_comparison) | ~12 | ~3,500+ |
| 2 | **35.semantics/lint docstring-skip helper (part 2)** | A | 5 lint files (security_missing_auth, security_raw_html, security_sql_injection, closure_capture, + remaining) | ~8 | ~700+ |
| 3 | **70.backend/backend type_mapper consolidation** | B + D | cranelift_type_mapper.spl, common/type_mapper.spl, llvm_type_mapper.spl, c_codegen_adapter.spl, (+ helper module if needed) | ~9 | ~1,400 |
| 4 | **70.backend/native isel_aarch64.spl + arm_neon helper** | B/C | isel_aarch64.spl, arm_neon.spl, (+ shared helper if pattern matches) | ~10 | ~960 |
| 5 | **70.backend/native x86_64_simd.spl SIMD codegen helper** | C | x86_64_simd.spl (within-file extract) | 1 | ~245 |
| 6 | **70.backend/backend vhdl_backend.spl within-file** | C | vhdl_backend.spl | 4 | ~482 |
| 7 | **70.backend/backend native_elf.spl** | C | native_elf.spl | 7 | ~448 |
| 8 | **70.backend/linker linker_wrapper consolidation** | D | linker_wrapper.spl, linker_wrapper_lib_support.spl, obj_taker.spl | ~4 | ~309 |
| 9 | **70.backend/backend remaining (cli_codegen, error_conversion, riscv_target, llvm_cross_target)** | B/C | 4 files | ~6 | ~350 |
| 10 | **80.driver driver_public_api.spl** | C | driver_public_api.spl | 11 | ~693 |
| 11 | **80.driver shb_reader.spl + build/main.spl** | C | shb_reader.spl, build/main.spl | 4 | ~518 |
| 12 | **90.tools fix/main.spl + ffi_gen/type_mapping.spl + header_gen/c_header.spl** | C/D | 3 files | ~14 | ~1,118 |
| 13 | **90.tools verify/compare_features.spl + remaining** | C | 1–2 files | ~4 | ~280 |
| 14 | **40.mono monomorphize/deferred_deserialize.spl** | C | deferred_deserialize.spl | 6 | ~469 |
| 15 | **30.types type_layout.spl** | C | type_layout.spl | 3 | ~328 |
| 16 | **10.frontend lexer.spl + parser_decls_use.spl + alloc_inference.spl** | C | 3 files | ~7 | ~528 |
| 17 | **10.frontend remaining (treesitter/outline_decls.spl, interpreter/cli_eval.spl, core/ast.spl)** | C | 3 files | ~6 | ~650 |
| 18 | **50.mir + 60.mir_opt + 99.loader long-tail** | C | 4 files | ~5 | ~120 |

**Total:** 18 batches, ~127 line-mode groups + 6 cosine-only additions, ~3,411 lines collapsed.

Cosine adds 6 findings vs line-mode (133 vs 127); the new `10.frontend/core/ast.spl` (impact 312) is folded into batch 17, the others into existing same-layer batches (1, 16, 18). No new batches needed — cosine confirms the line-mode hotspot order.

**Sub-batch breakdown for batch 1:**
- **1a — DONE 2026-04-27** (`nptolssx`): lint_text.spl (helper) + __init__.spl + security_hardcoded_secret.spl + lint_text_spec.spl. 4 files, 3 groups eliminated, 109 dup_lines collapsed.
- **1b — pending**: security_insecure_comparison.spl + security_sql_injection.spl + security_missing_auth.spl + security_raw_html.spl. 4 files. 2 simple cases, 2 with subtleties (missing_auth keeps `lines` for `_has_security_annotation` look-back; raw_html uses `cl.raw` for `_leading_spaces` indent tracking).
- **1c — pending**: security_ssrf.spl (2 loops) + mcp_perf_lint.spl (3 loops) + remote_exec_lint.spl (multiple loops). 3 files, more complex.

## Coupling spot-check shortlist (non-parser, ≥17 imports)

Per user direction: spot-check 3–5 worst non-parser high-fan-out files. Final shortlist:

1. `30.types/associated_types.spl` (26 imports) — type system, candidate for facade refactor
2. `30.types/variance.spl` (20 imports) — type system
3. `30.types/higher_rank_poly.spl` (20 imports) — type system
4. `70.backend/linker/linker_wrapper.spl` (21 imports) — already in batch 8
5. `10.frontend/core/ast_clone.spl` (18 imports) — AST utility

`80.driver/driver.spl` (40) skipped — it's the driver entry point, high fan-out is its job.

**Coupling treatment:** for each, attempt to identify a reusable facade (a single import that re-exports a curated subset). Ship only if the facade is clearly cleaner; otherwise file as a separate task with rationale.

## Risk register

| # | Risk | Mitigation |
|---|------|-----------|
| 1 | Bootstrap break per batch | Full `bootstrap-from-scratch.sh --deploy` after every commit (per user) |
| 2 | Lint loops are similar but not identical | Manual diff before extract; preserve any lint-specific tweaks via parameters |
| 3 | Cross-layer Pattern D may invert MDSOC dependency | Verify lower→higher direction; abandon move + file as design-intent if violation |
| 4 | Wrapper silent no-op (`--quiet` whole-tree returned 0 bytes) | Already worked around by per-layer runs |
| 5 | Coupling proxy may surface false positives (parsers high by design) | Only spot-check non-parser; do not refactor parsers without separate planning |
| 6 | TODO→NOTE temptation | Per `feedback_no_coverups.md` — never. Implement or delete entirely. |
| 7 | Parallel /dev tracks racing on same files | Pause other tracks before each commit (per `feedback_submodule_race_parallel_dev.md`) |
| 8 | Cosine job may surface new hotspot mid-cycle | Append as batches 19+; do not re-plan in flight unless impact > 500 |

## Layer order

Lower-layer changes first when batches cross layers:
- 30.types → 35.semantics → 40.mono → 50.mir → 60.mir_opt → 70.backend → 80.driver → 90.tools → 99.loader

But within-file (Pattern C) batches can ship in any order — they don't move imports.

## Phase 4 spec scope (advisor adjustment)

Per advisor: do not pin all current behavior with new specs. Existing test suite + bootstrap is the behavior-preserving gate. Phase 4 will write specs ONLY for hotspot helpers that are extracted (i.e. the new helper modules), not for every refactored file.

## Definition of done per batch

1. `bin/simple build lint` clean on touched files
2. `bin/simple build check` (lint + fmt --check + tests) passes
3. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` completes successfully
4. `bin/simple duplicate-check <touched-layer>` shows reduced group count for the targeted findings
5. `jj commit` with message `refactor(<area>): collapse <pattern> in <files>`
6. State file `## Phase Outputs / ### 5-implement` updated with batch number, files, before/after group counts
