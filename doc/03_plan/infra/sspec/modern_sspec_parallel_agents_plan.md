# Modern SSpec Completion — Parallel Small-Agent Implementation Plan

**Date:** 2026-08-08
**Research:** `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md`
**Design:** `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`
**Process:** SPipe phases (`.claude/skills/spipe.md`, `.claude/agents/spipe/*.md`); Codex lanes via `$sp_dev`.

> **Status note (2026-08-08, late revision):** this file was repeatedly reverted to a
> mid-session snapshot by a concurrent peer session syncing a stale local checkout —
> the same anti-pattern documented in `.claude/rules/vcs.md` § "Sync must never
> clobber." Prior status edits landed correctly in their own commits but were then
> overwritten by an unrelated sync commit that carried an older copy of this exact
> file. This revision restates the full status table in one place so it cannot
> silently drift out of a single narrow diff again.

## Agent model

Small, cheap agents (Codex Spark / Haiku / Sonnet / GLM sidecars) do scoped implementation and verification lanes; **every lane result is reviewed by a higher-capability model (Fable/Opus) before acceptance** — verify SHAs, run receipts, and deliberate-red evidence yourself; rework goes back to the ORIGINAL lane with guidance (see memory rule feedback_review_every_subagent_result_with_higher_model). No lane self-certifies. Placeholder helpers must fail explicitly (`assert(false)`/`fail(...)`), never silently pass.

Ownership mirrors the spec-to-spipe agent rules: one shared-contract owner, one verification owner, one `spipe_docgen` integrator.

## Waves and lanes

### Wave 0 — contract + red-team gates (blocks everything)

| Lane | Exclusive ownership | Deliverable | Status |
|---|---|---|---|
| E0 Evidence contract | `src/lib/common/spec/evidence/**`, manifest schema, compatibility facade | frozen v1 evidence model + golden serialization | **LANDED** — `model.spl`, `evidence_comparator.spl`, spec `test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl` (28 examples after hardening) |
| E1 Verification/red team | evidence acceptance policy, release checks | deliberate-red, stale-hash, unresolved-selector, vacuity, example-integrity gates | **LANDED, defects fixed** — first red-team pass (`doc/08_tracking/audit/modern_sspec_evidence_contract_redteam_2026-08-08.md`) found 4 defects (F1 bind-only vacuity, F2 non-numeric tolerance, F3 tolerance overflow, F4 unchecked manifest hex length); **all four fixed** in `evidence_comparator.spl`/`model.spl` (`check_is_positive` excludes binds, `is_numeric_text`/`within_tolerance` guard the tolerance path, `is_sha256_hex` gates manifest digests) with regression coverage in `typed_evidence_oracle_spec.spl`. A second red-team pass over the seven lane modules (`doc/08_tracking/audit/modern_sspec_lane_modules_redteam_2026-08-08.md`) found and fixed 2 further real defects: `terminal_grid.spl` region-bounds fabrication and `binary_layout.spl`'s wide-field table hex truncation, both with regression tests. |

Merge gate satisfied: E0+E1 schema, failure semantics, and deliberate-red fixtures agreed and landed. No other lane edited shared records without going through this gate.

### Wave 1 — independent domain foundations (parallel, dep: E0)

| Lane | Exclusive ownership | Status |
|---|---|---|
| E2 TUI provider | ui_access/SGTTI/Draw IR/wm_compare adapters, TUI cell grid | **LANDED** — `src/lib/common/spec/evidence/format/terminal_grid.spl`, spec `terminal_grid_spec.spl` (21 examples incl. region-bounds hardening) |
| E2b GUI action trace | interaction sequence, bounded settling | **LANDED** — `src/lib/common/spec/evidence/action_trace.spl`, spec `action_trace_spec.spl` (14 examples) |
| E3 Text protocol | text parser, grammar adapter, selectors, structural comparator | **LANDED** — `src/lib/common/spec/evidence/format/text_protocol.spl`, spec `text_protocol_spec.spl` (7 examples) |
| E4 Binary layout | BinaryLayoutIR, PTE accessor adapter, RegisterIR/struct bridges | **LANDED** — `src/lib/common/spec/evidence/format/binary_layout.spl`, spec `binary_layout_spec.spl` (10 examples incl. wide-field-table hardening), mirrors `src/os/kernel/types/bitfield.spl` |
| E5 Docgen skeleton | SOLE `spipe_docgen` owner: evidence loader + generic ManualBlock renderer | **LANDED** — `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl` reads an optional `<spec>.evidence.sdn` sidecar and calls `manual_render.render_blocks`; `generator.spl` appends a `## Typed Evidence` section only when the sidecar produced blocks. Proven byte-identical-output-when-absent (`test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl`, 2 examples) AND proven against the REAL live `generate_feature_doc` entry point across two independent invocations (`test/02_integration/app/spipe_docgen_regeneration_live_spec.spl`, 4 examples; `scripts/check/check-spipe-docgen-regeneration-live.shs`). |
| E6 Spec-to-SPipe bridge | `simple.sspec.evidence.ext.v1` extension namespace + emitter integration (frozen Phase-0 core untouched) | **LANDED** — `src/lib/common/spec/evidence/spipe_extension.spl` (namespace + records) plus `src/app/spec_to_sspec/spipe_evidence_emit.spl`, wired into `main.spl`'s real `--apply`/`-o` write path (6 examples, `spipe_evidence_emit_spec.spl`). Caveat, unchanged: `main.spl` is a line-scanning text modernizer with no semantic node model, so there is no manifest field to write an extension value into — the adapter writes an additive `<path>.spipe-evidence.txt` sidecar via `extension_lines` instead. Genuinely wired into live emitter output, not a manifest-field write, because no manifest exists here. |

### Wave 2 — reference profiles + examples

E2/E3/E4's format-adapter modules are landed (Wave 1 rows above); their generated-manual
half is proven through E5's live-docgen wiring. E7 (domain profiles) is **fully landed**:

| Lane | Exclusive ownership | Status |
|---|---|---|
| E7a 2D/3D scene | draw-node trees, 3D scene-graph assets | **LANDED** — `src/lib/common/spec/evidence/format/scene_profile.spl`, spec `scene_profile_spec.spl` (19 examples) |
| E7b Simulation/stats | timeline, invariants, KPI tolerances, sample distributions | **LANDED** — `src/lib/common/spec/evidence/format/simulation_profile.spl`, spec `simulation_profile_spec.spl` (13 examples) |
| E7c Audio profile | RMS/peak/silence-ratio, pure-integer arithmetic | **LANDED** — `src/lib/common/spec/evidence/format/audio_profile.spl`, spec `audio_profile_spec.spl` (8 examples) |
| E7d ML profile | dataset/model hash + seed mandatory, tolerance-needs-reason | **LANDED** — `src/lib/common/spec/evidence/format/ml_profile.spl`, spec `ml_profile_spec.spl` (13 examples) |
| E7e JSON/JSON-Pointer adapter | RFC 6901 pointer paths, real JSON parser reuse | **LANDED** — `src/lib/common/spec/evidence/format/json_document.spl`, spec `json_document_spec.spl` (8 examples) |

Every E7 lane landed with a sabotage/revert proof. **What E7 does NOT include**: live capture
from real hardware/GPU/TUI/simulation sources — every domain module above takes constructed
input. Two modules elsewhere in the tree (`exec_capture.spl`, `file_capture.spl`, see E8) do
capture from a genuinely running process or real file; extending that to the domain profiles
above is real, separately-scoped future work, not part of E7's own defined deliverable.

### Wave 3 — migration, docs, final review

| Lane | Deliverable | Status |
|---|---|---|
| E8 Migration/examples | three runnable reference specs, byte-identical regeneration, legacy adapter migration; never hand-edits generated manuals | **LANDED** (core deliverable) + **ongoing backlog** (see below). Three reference example manuals landed (`test/03_system/tools/spipe/examples/`: interactive 4 examples, protocol 4 examples, binary 5 examples — all fixture-driven with an honest docstring saying so, never hand-edited). Byte-identical regeneration: `regeneration_gate.spl` (4 examples) + `scripts/check/check-sspec-evidence-regeneration.shs` (fixture-level CI check) + `scripts/check/check-spipe-docgen-regeneration-live.shs` + `spipe_docgen_regeneration_live_spec.spl` (4 examples, proven against the real live entry point). Legacy adapter migration: TWO adapters landed — `legacy_facade.spl` for specs already using `ScenarioEvidenceArtifact` (corpus exhausted at exactly 4 real specs, confirmed by full-repo search, documented in `doc/07_guide/infra/sspec_legacy_migration.md`) and `untyped_capture.spl` for specs with a real capture but no typed wrapper (design: `doc/05_design/infra/sspec/untyped_evidence_migration_design.md`). Two live (not fixture) capture modules: `exec_capture.spl` (real process, 6 examples) and `file_capture.spl` (real file I/O, 7 examples, 2 blocked on a seed/self-hosted `byte_at` builtin gap, not a code defect). |
| E8-backlog Untyped-evidence corpus migration | migrate the remaining `untyped_capture` candidates | **OPEN, bounded and tracked** — `scripts/check/scan-untyped-evidence-candidates.shs` enumerates the full population: 1119 category-1 candidates across 414 files (`doc/08_tracking/audit/untyped_evidence_migration_candidates_2026-08-08.md`). 30 migrated ('yes') and 135 explicitly rejected with recorded reasons to date, across 8 worked batches (see `doc/08_tracking/todo/untyped_evidence_migration_backlog_2026-08-08.md` for the full migrated-file list). Yield rate is declining sharply as the easy front-loaded wins are exhausted (roughly 5/8 -> 1/24 -> 0/26 -> 1/41 accepted per batch) — most of the remaining ~954 unmarked rows skew toward the scanner's known false-positive class (static `file_read` source-text checks). This is real, correctly-scoped, incremental work with no natural single-session completion point; each future session should pull the next unmigrated block from the audit doc and apply the same per-candidate triage rule. |
| E9 Docs/skills | requirements/design/plan/guide/skills/templates refresh (list below) in the SAME change as the executable workflow | **LANDED** — `doc/02_requirements/feature/sspec_scenario_manual.md` (FR-7..FR-14 added, FR-14 status updated to LANDED), `doc/05_design/sspec_capture_extension.md` superseded-note added, `doc/03_plan/sspec_modernization_plan.md` (Superseded note + status section), `doc/07_guide/infra/sspec_typed_evidence.md` + `_tldr.md` (new, full operator guide), `doc/07_guide/infra/sspec_legacy_migration.md` (new, migration pattern + sweep progress), `.claude/skills/spipe.md` (Typed evidence reference card), `.claude/agents/spipe/spec.md` (typed-evidence oracle guidance), `.codex/skills/sp_dev/SKILL.md` (mirrored reference card), `.claude/templates/spipe_template.spl` (commented example block), `doc/00_llm_process/feature_expert/modern_sspec/skill.md` (LLM wiki entry, 158 lines), `.claude/rules/testing.md` (typed-evidence fail-closed rules subsection), `doc/glossary.md` (9 new terms). |
| E1 Final verification | independent deliberate-red + freshness review; no stale/missing/aspirational example accepted | **LANDED** — two independent red-team passes (contract-level and lane-module-level, both cited above) found 6 total defects; all 6 fixed with regression coverage; every fix independently re-verified by re-running the affected specs before landing, not just trusted from the fixing agent's report. Documentation freshness enforced by this very revision — a stale status table is exactly the class of defect this gate exists to catch. |

### Contention rules
- E0 alone changes shared evidence records; E1 alone changes acceptance policy; E5 alone changes `spipe_docgen`; E6 alone changes shared spec-to-spipe emitter integration.
- Adapter lanes own only their provider/format/comparator/test directories.
- A shared-field change needs migration + compatibility + golden update + E1 review.

## Documents and tools E9 updates together

```text
doc/02_requirements/feature/sspec_scenario_manual.md   (FR-7..FR-14 — LANDED)
doc/05_design/sspec_capture_extension.md               (superseded note — LANDED)
doc/03_plan/sspec_modernization_plan.md                (status section — LANDED)
doc/07_guide/infra/sspec_scenario_manual.md            (existing guide, cross-referenced by the new typed-evidence guide)
.claude/skills/spipe.md                                (decision table + reference card — LANDED)
.claude/agents/spipe/spec.md                           (typed-evidence oracle guidance — LANDED)
.codex/skills/sp_dev/SKILL.md  + .agents/skills mirror (LANDED; no .gemini/commands spipe-mirror pattern exists in this repo)
.claude/templates/spipe_template.spl                   (commented example — LANDED)
```

Tool additions delivered: `scripts/check/check-sspec-evidence-regeneration.shs`,
`scripts/check/check-spipe-docgen-regeneration-live.shs`,
`scripts/check/scan-untyped-evidence-candidates.shs`. The `sspec-maintain evidence
<spec> --explain` / `--profile-completeness` / `simple test --update-evidence` command
surface described in `doc/05_design/infra/sspec/sspec_maintain_evidence_findings.md`
remains a design, not yet implemented in `src/app/sspec_maintain/` — this is separate,
scoped future work with its own design doc, not an unscoped gap.

## Completion gates

The acceptance gates in research doc §10: three executable reference specs (LANDED);
deterministic regenerated manuals bound to spec SHA-256 + run identity + artifact hashes
(LANDED — `EvidenceManifest`/`evidence_manifest_is_complete` enforce 64-hex digests, and
the regeneration gate proves determinism at both fixture and live-pipeline level);
deliberate-red per oracle (LANDED — every landed module has a sabotage/revert proof);
TUI Unicode fixtures (LANDED — combining/emoji/wide fixtures in `terminal_grid_spec.spl`);
GUI policy compliance (LANDED — `action_trace.spl`'s `should_capture_gui_image`); text
protocol exact/ignore/pattern/order/multiset/correlation/malformed/closed proofs (LANDED);
binary via real PTE accessors (LANDED); wm_compare exact gates unchanged (untouched by
this work, confirmed); spec-to-spipe agreement without tautologies (LANDED, E6); skills/
guides refreshed in-change (LANDED, E9). Documentation freshness is part of completion —
this revision is itself evidence of that gate being actively enforced, not waived.

**What remains open, precisely:** the E8-backlog row above (1089 of 1119 known untyped-
evidence candidates), and building real live-capture infrastructure for the E7 domain
profiles (TUI/GPU/simulation/hardware) beyond the two process/file capture modules already
landed. Both are real, separately-scoped, multi-session efforts — not gaps in the lanes
defined and completed above.

## Immediate order

Original ordering (research doc §11) is complete: freeze contract → red verifier →
text+binary comparators → TUI grid → GUI trace → docgen projection → three examples →
spec-to-spipe → domain profiles → migration → docs → independent review. Next work, when
picked up, should pull from the E8-backlog audit doc in file order and/or scope a new
lane for live-capture infrastructure per domain profile.
