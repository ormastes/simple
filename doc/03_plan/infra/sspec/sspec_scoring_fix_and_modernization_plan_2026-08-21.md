# SSpec Scoring Fix + Low-Scorer Modernization Plan

**Date:** 2026-08-21
**Context:** follows `modern_sspec_parallel_agents_plan.md` / `modern_sspec_completion_plan_2026-08-09.md` (all lanes LANDED; E8-backlog open). This plan covers (1) the scorer defects found when the updated bitfield/binary tests were scored, and (2) the first bounded modernization batches for low-scoring specs.

## Phase 1 — scorer fixes (DONE, commits c02ce1f1a90 + 4cce48b99d6)

The `sspec-maintain` scorer mis-scored binary/UI specs in four ways, all fixed with regression coverage in `test/01_unit/app/sspec_maintain/scoring_spec.spl` (19/19, rule_coverage 5/5, cache 6/6):

| # | Defect | Fix |
|---|---|---|
| 1 | Capture detection knew only `capture_`/`@capture`/`evidence(` — every modern typed-evidence call (`evidence_manifest(`, `render_manual(`, `terminal_grid`, `gui_image`, `action_trace`, `binary_layout`, `bit_table`, `.evidence.sdn`) was invisible → false SSDOC-EVD-001 | `source_facts.spl` recognizes the modern capture surface |
| 2 | Manual evidence detection matched ` ```textgrid `/` ```protocol ` fences the renderer never emits (it emits ` ```text `, `unknown-block:`, `## Provenance`, images) → false SSDOC-EVD-003 | match real `manual_render.spl` output |
| 3 | Standalone assertions (`assert_equal/true/false/not_equal/contains/nil`) didn't count as oracles → false ORA-001 blocker on all six `binary_*_spec` families | `_is_real_assertion` + assertion counting include them, with literal-tautology exclusions |
| 4 | `var found = false` … loop … `expect(found).to_equal(false)` tripped the binding-equality tautology heuristic → false ORA-002 on `scene_profile_spec` | only immutable `val` bindings feed the heuristic |

**Operational note:** the scan cache at `.simple/cache/sspec-maintain` keys on source hash only, NOT scorer version — after any scorer change, `rm -rf .simple/cache/sspec-maintain` (cost us a false "fix didn't work" round). Fixing that keying is follow-up work.

Result on `test/01_unit/lib/common/spec/evidence/` (23 specs): oracle blockers 7 → 0. Remaining: 18 × SSDOC-TRC-003 (file-top `# @req REQ-…` IDs not bound inside any scenario) — genuine content debt, Phase 2's target.

## Census (grep-based, 2026-08-21, ~20.5k specs)

| dir | specs | pass_todo (ORA-001 class) | no REQ- (TRC-001 class) | no step( (BEH-001 class) |
|---|---|---|---|---|
| 00_formal_verification | 22 | 0 | 22 | 22 |
| 01_unit | 8618 | 13 | 8161 | 7997 |
| 02_integration | 772 | 5 | 733 | 704 |
| 03_system | 3472 | 4 | 3031 | 2711 |
| 05_perf | 109 | 0 | 105 | 96 |
| feature | 352 | 1 | 344 | 347 |
| integration | 589 | 5 | 583 | 587 |
| system | 1859 | 0 | 1774 | 1852 |
| unit (mirror) | 5201 | 12 | 5098 | 5114 |

Modern-SSpec adoption outside the typed-evidence lane is near zero (~95%+ of specs lack REQ bindings and step calls). Whole-tree modernization is a multi-quarter effort; this plan starts the highest-value batches only.

## Phase 2 — modernization batches (this session, ≤4 parallel agents, separate worktrees)

Priority order (highest value per effort first — specs already closest to modern):

| Batch | Files | What "modern" means here | Done |
|---|---|---|---|
| B1 binary layout specs | `binary_layout_spec`, `binary_layout_schema_spec`, `binary_compare_spec`, `binary_domains_spec`, `binary_embedded_domains_spec`, `binary_protocol_domains_spec`, `binary_algorithm_domains_spec`, `format/stacked_md_table_spec` | bind file-top `@req` IDs inside each scenario (`# @req: REQ-…`), authored purpose docstring, outcome-named its, step() in narrative scenarios | **DONE** `70d276e000f` — all 8 uncapped, raw 68-78 → 81-85; all green (66 examples, 0 failed) |
| B2 evidence profiles/UI | `terminal_grid_spec`, `action_trace_spec`, `text_protocol_spec`, `scene_profile_spec`, `simulation_profile_spec`, `audio_profile_spec`, `ml_profile_spec`, `json_document_spec`, `typed_evidence_oracle_spec`, `untyped_capture_spec`, `legacy_facade_spec`, `manual_render_spec`, `regeneration_gate_spec`, `exec_capture_spec`, `file_capture_spec`, `format/*` (non-binary) | same | **DONE** `3d804e0fbc5` — 15 files, blockers 0, raw 68-80 → 72-89; 4 files keep TRC-001 (no REQ id exists to bind); 14/15 specs RED pre-existing (seed `undefined field 'mode'` bug, identical counts pre/post edit — NOT caused by this batch) |
| B3 spipe examples | `test/03_system/tools/spipe/examples/*.spl` (12 specs incl. live_* captures) | same; these are the reference manuals — keep byte-identical regeneration green | **DONE** `e6ab8c5cdc6` — 5 TRC-003 blockers cleared, raw 74-82 → 83-89; regeneration gate `PASS — 4 example(s), 0 failed`; several specs RED pre-existing (same seed bug, verified against pristine HEAD) |
| B4 pass_todo blockers | the 40 specs listed by `grep -rl pass_todo test/ --include='*_spec.spl'` | replace unconditional pending scaffold with a real oracle or delete the spec (per testing.md ORA-001 policy) | **DONE** `14121ffde6a` — 39/40 were scorer FALSE POSITIVES (`_is_pending` matched any mention of `pass_todo`/`pending`, incl. fixture strings and expect args); fixed to statement-position detection only. ORA-001 count 40 → 1. Remaining RED: `test/feature/usage/pass_variants_spec.spl` genuinely executes placeholder statements by design — needs an `@exercises:` scorer exemption (follow-up) |

## Post-batch verification (2026-08-21)

- Oracle blockers in `test/01_unit/lib/common/spec/evidence/`: 0 (grep ORA-001\|ORA-002 = 0 across all 23 specs).
- `scoring_spec` 19/19, `rule_coverage_spec` 5/5 after the B4 scorer change (run in the main worktree).
- B3 dir scan: 0 blockers across all 12 specs (cache cleared).
- Pre-existing seed bug NOT fixed (out of scope, not easy): semantic error `undefined field 'mode': cannot access field on value of type 'function'` — fires in `std.common.spec.evidence.model` consumers (`check.mode` field access at model.spl:243+ resolves the field as a function under the current seed). Reds ~15 evidence specs + several spipe example specs, identical before/after all batches. Filed as the follow-up below.

## Follow-ups (not done this session)

1. Seed bug: `.mode` struct-field access mis-resolved as function in evidence model consumers.
2. Scan-cache keying: fold scorer/rule version into `sspec_cache_identity` so cache invalidates on scorer change.
3. `@exercises:` exemption directive for specs whose subject IS placeholder-statement execution (`pass_variants_spec`).
4. TRC-001 for the 4 evidence specs with no REQ identity: author stable REQ ids, then bind.

Rules for every batch: only edit the listed specs; never weaken assertions; each touched spec must still pass `bin/simple test <spec>` (results line required, not exit 0); rescan with `bin/simple src/app/sspec_maintain/main.spl scan <spec>` (cache cleared) and record before/after `raw=`; commit per batch on main via the main worktree.

## Verification

After each batch lands: re-run the batch's specs + `scoring_spec`, rescan the batch dir, update this table's Done column with raw= movement. "How much done" = this table plus the census row deltas for the touched dirs.
