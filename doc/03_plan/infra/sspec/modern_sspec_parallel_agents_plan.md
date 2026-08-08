# Modern SSpec Completion — Parallel Small-Agent Implementation Plan

**Date:** 2026-08-08
**Research:** `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md`
**Design:** `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`
**Process:** SPipe phases (`.claude/skills/spipe.md`, `.claude/agents/spipe/*.md`); Codex lanes via `$sp_dev`.

## Agent model

Small, cheap agents (Codex Spark / Haiku / Sonnet / GLM sidecars) do scoped implementation and verification lanes; **every lane result is reviewed by a higher-capability model (Fable/Opus) before acceptance** — verify SHAs, run receipts, and deliberate-red evidence yourself; rework goes back to the ORIGINAL lane with guidance (see memory rule feedback_review_every_subagent_result_with_higher_model). No lane self-certifies. Placeholder helpers must fail explicitly (`assert(false)`/`fail(...)`), never silently pass.

Ownership mirrors the spec-to-spipe agent rules: one shared-contract owner, one verification owner, one `spipe_docgen` integrator.

## Waves and lanes

### Wave 0 — contract + red-team gates (blocks everything)

| Lane | Exclusive ownership | Deliverable | Status |
|---|---|---|---|
| E0 Evidence contract | `src/lib/common/spec/evidence/**`, manifest schema, compatibility facade | frozen v1 evidence model + golden serialization | **LANDED** 2026-08-08 — `model.spl`, `evidence_comparator.spl`, spec `test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl` (24 examples) |
| E1 Verification/red team | evidence acceptance policy, release checks | deliberate-red, stale-hash, unresolved-selector, vacuity, example-integrity gates | Red-team pass run 2026-08-08 (`doc/08_tracking/audit/modern_sspec_evidence_contract_redteam_2026-08-08.md`); found 4 open defects (F1-F4: bind-only vacuity, non-numeric tolerance, tolerance overflow, unchecked manifest hex length) **not yet fixed** in `evidence_comparator.spl`/`model.spl` — gates E2-E7 adoption per the audit's own recommendation |

Merge gate: E0+E1 agree on schema, failure semantics, deliberate-red fixtures. No other lane edits shared records.

### Wave 1 — independent domain foundations (parallel, dep: E0)

| Lane | Exclusive ownership | Status |
|---|---|---|
| E2 TUI provider | ui_access/SGTTI/Draw IR/wm_compare adapters, TUI cell grid | **LANDED** — `src/lib/common/spec/evidence/format/terminal_grid.spl`, spec `terminal_grid_spec.spl` (19 examples) |
| E2b GUI action trace | interaction sequence, bounded settling | **LANDED** — `src/lib/common/spec/evidence/action_trace.spl`, spec `action_trace_spec.spl` (14 examples) |
| E3 Text protocol | text parser, grammar adapter, selectors, structural comparator | **LANDED** — `src/lib/common/spec/evidence/format/text_protocol.spl`, spec `text_protocol_spec.spl` (7 examples) |
| E4 Binary layout | BinaryLayoutIR, PTE accessor adapter, RegisterIR/struct bridges | **LANDED** — `src/lib/common/spec/evidence/format/binary_layout.spl`, spec `binary_layout_spec.spl` (9 examples), mirrors `src/os/kernel/types/bitfield.spl` |
| E5 Docgen skeleton | SOLE `spipe_docgen` owner: evidence loader + generic ManualBlock renderer | **LANDED** — `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl` reads an optional `<spec>.evidence.sdn` sidecar and calls `manual_render.render_blocks`; `generator.spl` appends a `## Typed Evidence` section only when the sidecar produced blocks, proven byte-identical-output-when-absent by `test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl` (2 examples) |
| E6 Spec-to-SPipe bridge | `simple.sspec.evidence.ext.v1` extension namespace + emitter integration (frozen Phase-0 core untouched) | **LANDED** — `src/lib/common/spec/evidence/spipe_extension.spl` (namespace + records) plus `src/app/spec_to_sspec/spipe_evidence_emit.spl`, wired into `main.spl`'s real `--apply`/`-o` write path (6 examples, `spipe_evidence_emit_spec.spl`). Caveat: `main.spl` is a line-scanning text modernizer with no semantic node model, so there is no manifest field to write an extension value into — the adapter instead writes an additive `<path>.spipe-evidence.txt` sidecar via `extension_lines`. Genuinely wired into live emitter output, not a manifest-field write, because no manifest exists here. |

### Wave 2 — reference profiles + examples

E2/E3/E4 each land their reference profile + generated manual (deps: own lane + E5) — the
profile modules themselves are landed (see Wave 1 rows above); the "generated manual" half
is blocked on E5, which is still open. E7 (domain profiles: 2D, 3D, simulation, audio,
stats, ML) deps E0 + relevant adapters — **partially landed**:

| Lane | Exclusive ownership | Status |
|---|---|---|
| E7a 2D/3D scene | draw-node trees, 3D scene-graph assets | **LANDED** — `src/lib/common/spec/evidence/format/scene_profile.spl`, spec `scene_profile_spec.spl` (19 examples) |
| E7b Simulation/stats | timeline, invariants, KPI tolerances, sample distributions | **LANDED** — `src/lib/common/spec/evidence/format/simulation_profile.spl`, spec `simulation_profile_spec.spl` (13 examples) |
| E7 audio / ML profiles | — | **LANDED** — `format/audio_profile.spl` (RMS/peak/silence-ratio, pure-integer isqrt, no f64; 8 examples) and `format/ml_profile.spl` (dataset/model hash + seed mandatory, tolerance-needs-reason, empty-set refused; 13 examples), each with sabotage/revert proof. |

E6 lands generated SSpec/evidence/manual fixtures — **OPEN**, no such generated fixtures found.

### Wave 3 — migration, docs, final review

| Lane | Deliverable | Status |
|---|---|---|
| E8 Migration/examples | three runnable reference specs, byte-identical regeneration, legacy adapter migration; never hand-edits generated manuals | **PARTIAL** — the three reference example manuals landed (interactive/protocol/binary, `test/03_system/tools/spipe/examples/`, all fixture-driven with an honest docstring saying so). Two modules now capture from ACTUALLY RUNNING/on-disk sources rather than constructed input: `format/exec_capture.spl` (a real process, proven with `true`/`false`/`echo`/a nonexistent command; 6 examples) and `format/file_capture.spl` (a real file on disk, sha256-recomputed per capture, proven by writing two different files to one path across two examples and asserting the hashes differ; 7 examples, 2 of which pipe through `json_document` and could not be re-run under the Rust seed fallback used during this landing — `method byte_at not found`, a seed/self-hosted builtin gap, not a code defect, since `json_document`'s own spec already passed 8/0 under self-hosted; self-hosted re-verification owed). `legacy_facade.spl` (FR-14, see requirements doc) is landed: old-style `ScenarioEvidenceArtifact` captures now convert losslessly into the typed pipeline and render through the same `manual_render`. `regeneration_gate.spl` implements the byte-identical-regeneration acceptance criterion (digest-based, distinguishes fields that legitimately vary run-to-run from a `spec_sha256` mismatch that means the manual is stale; 4 examples). Every other module besides exec_capture/file_capture remains fixture-driven. Legacy adapter migration now has a concrete, verified proof rather than staying theoretical: `test/01_unit/app/simple_lab/lab_html_render_spec.spl` (4/4) and `test/01_unit/lib/common/spec/scenario_helpers_spec.spl` (53/53) each gained an additive typed-evidence check via `legacy_evidence_to_canonical` + `compare_evidence`, with every pre-existing assertion untouched and a sabotage/revert proof that the new checks are load-bearing. Pattern documented in `doc/07_guide/infra/sspec_legacy_migration.md`. Migration corpus is now EXHAUSTED for direct `scenario_helpers`/`scenario_evidence` constructor usage: 4 specs migrated (`lab_html_render_spec.spl`, `scenario_helpers_spec.spl`, `legacy_facade_spec.spl`, `scenario_evidence_spec.spl`), and a full repo search found no more real (non-string-literal, currently-passing) candidates — one candidate (`mcp_stdio_integration_spec.spl`) was investigated and rejected because it imports but never calls the helpers, and 2 of its 3 examples already fail before any edit. The remaining migration surface is therefore NOT these constructors — it is specs that use ad-hoc string/print-based evidence with no typed structure at all, which need a different (probably per-spec) migration approach, not this facade. That surface is now BOUNDED, not undefined: `scripts/check/scan-untyped-evidence-candidates.shs` enumerates it at **1119 category-1 candidates across 414 files** (`doc/08_tracking/audit/untyped_evidence_migration_candidates_2026-08-08.md`). 2 of these are already migrated via `untyped_capture.spl` (`process_ops_ext_spec.spl`, `timeout_spec.spl`). The remaining 1117 are a known, finite, per-spec triage queue — each still needs the manual category confirmation the design doc requires, but the population is no longer unknown. The regeneration gate is now wired into a runnable CI-style check (`scripts/check/check-sspec-evidence-regeneration.shs`, PASS/FAIL/ERROR verdict-line convention matching sibling `scripts/check/*.shs`, fail-closed ERROR on an empty target range; `test/02_integration/app/sspec_evidence_regeneration_gate_spec.spl`, 3 examples), proven against the same representative fixtures the unit spec uses — this proves the gate mechanism is runnable in CI style, not that it is hooked into a live `spipe_docgen` run (which reads a rendered sidecar file today, not evidence objects directly). **This gap is now closed**: `test/02_integration/app/spipe_docgen_regeneration_live_spec.spl` (4 examples) and `scripts/check/check-spipe-docgen-regeneration-live.shs` exercise the REAL `generate_feature_doc` entry point twice against the same spec + evidence sidecar and prove byte-identical output, covering both the determinism and the with/without-evidence contract. `generator.spl`/`evidence_loader.spl` were proven, not modified. |
| E9 Docs/skills | requirements/design/plan/guide/skills/templates refresh (list below) in the SAME change as the executable workflow | **OPEN** — this plan and the guide were refreshed 2026-08-08, but the requirements/design/skills/template documents listed below were not audited as part of this pass |
| E1 Final verification | independent deliberate-red + freshness review; no stale/missing/aspirational example accepted | **IN PROGRESS** — the 2026-08-08 red-team pass (see E1 above) is one such review and found 4 open defects; final sign-off still pending a fix + re-verify cycle |

### Contention rules
- E0 alone changes shared evidence records; E1 alone changes acceptance policy; E5 alone changes `spipe_docgen`; E6 alone changes shared spec-to-spipe emitter integration.
- Adapter lanes own only their provider/format/comparator/test directories.
- A shared-field change needs migration + compatibility + golden update + E1 review.

## Documents and tools E9 updates together

```text
doc/02_requirements/feature/sspec_scenario_manual.md   (FR-7..FR-14 added)
doc/05_design/sspec_capture_extension.md               (replace monolithic Capture)
doc/03_plan/sspec_modernization_plan.md                (rewrite around this wave graph)
doc/07_guide/infra/sspec_scenario_manual.md            (three full examples + cookbook)
.claude/skills/spipe.md                                (decision table + 3 short examples)
.claude/agents/spipe/spec.md
.codex/skills/sp_dev/SKILL.md  + .agents/skills / .gemini/commands mirrors
.claude/templates/spipe_template.spl
```

Tool additions (extend, don't replace `simple test` / `sspec-maintain`):
`sspec-maintain evidence <spec> --explain`, `sspec-maintain verify-examples`,
`sspec-maintain scan --profile-completeness`, `simple test <spec> --update-evidence|--accept-evidence`
(new/changed evidence stays pending-review). New findings SSDOC-EVD-101..107, SSDOC-UI-101/102, SSDOC-TUI-101, SSDOC-PROTO-101/102, SSDOC-BIN-101/102, SSDOC-MAN-101 (definitions in research doc §9).

## Completion gates

The acceptance gates in research doc §10 apply verbatim: three executable reference specs; deterministic regenerated manuals bound to spec SHA-256 + run identity + artifact hashes; deliberate-red per oracle; TUI Unicode fixtures; GUI policy compliance; text protocol exact/ignore/pattern/order/multiset/correlation/malformed/closed proofs; binary via real PTE accessors; wm_compare exact gates unchanged; spec-to-spipe agreement without tautologies; skills/guides refreshed in-change. Documentation freshness is part of completion, not release cleanup.

## Immediate order

Follow research doc §11: freeze contract → red verifier → text+binary comparators → TUI grid → GUI trace → docgen projection → three examples → spec-to-spipe → domain profiles → migration → docs → independent review.
