# Modern SSpec (Typed Evidence) Feature Expert

## Role

Own feature-specific process knowledge for **Modern SSpec typed evidence**
(evidence manifest schema `simple.sspec.evidence.v1`): a fail-closed pipeline
of typed selectors, oracle checks, and comparison results that lets a spec
assert against structured evidence (protocol fields, JSON pointers, terminal
regions, pixel regions, byte/bit ranges, scene paths) instead of loose text
matching, while keeping capture-runtime code and the docgen renderer in
separate processes that share only files.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Research: [doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md](../../../01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md)
- Design: [doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md](../../../05_design/infra/sspec/modern_sspec_typed_evidence_design.md)
- Plan (wave breakdown E0-E9, design authority for scope/sequencing):
  [doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md](../../../03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md)
- Layer expert: [layer_expert/test_runner](../../layer_expert/test_runner/skill.md)
- Related feature: [prevention_mocks](../prevention_mocks/skill.md) (separate
  fail-closed idiom, same "observation is not an oracle" family of traps)

## What landed today (2026-08-08, wave E0)

- **`src/lib/common/spec/evidence/model.spl`** — pure records only, no
  acquisition/parsing/rendering code (deliberately, so a capture-runtime
  object's render method can never be invoked cross-process by docgen):
  - `EvidenceSelectorKind` (`canonical_node`, `protocol_field`,
    `json_pointer`, `terminal_region`, `pixel_region`, `byte_range`,
    `bit_range`, `binary_field`, `scene_path`, `simulation_signal`) +
    `EvidenceSelector` (`kind`, `path`, `start`, `length`, `cardinality`,
    `optional`) — `cardinality` is the number of nodes the selector MUST
    resolve to; `-1` means "at least one".
  - `OracleMode`, `OracleCheck`/`OracleSpec` — the typed assertion layer over
    selectors.
  - `CanonicalEvidence`/`EvidenceNode` — the resolved evidence tree a spec
    checks against.
  - `ComparisonResult` — the pass/fail verdict record with per-check detail.
  - `ManualBlock` — a generic, renderer-agnostic record; providers emit these
    and `spipe_docgen` stays the sole Markdown renderer (this is the fix for
    the cross-process render problem below).
  - `EVIDENCE_MANIFEST_SCHEMA: text = "simple.sspec.evidence.v1"`.
- **`src/lib/common/spec/evidence/evidence_comparator.spl`** —
  `compare_evidence` and the fail-closed gates: `resolve_nodes` (exact path
  match against `evidence.nodes`), `cardinality_error` (0 nodes = "resolved
  no node", not silently satisfied), anchored pattern-class matching
  (`pattern_matches`: `hex:16`/`digit:3`/`alnum:*` class tokens, never
  regexes, always matched against the WHOLE selected scalar — a merely
  prefixed value fails).
- **Proof**: `test/01_unit/lib/common/spec/evidence/typed_evidence_oracle_spec.spl`
  (path as declared by the landing work; not present in every worktree copy
  of this repo as of this writing — confirm it exists before citing it as
  currently-green in a parallel session, this tree may be stale relative to
  origin).

## Implementation status (audit-verified 2026-08-09 against origin/main)

The "E2-E9 design-only" claim this section previously carried was STALE — it
described the E0-era state and was never updated when the later waves landed,
violating this file's own Update Rule. Corrected, verified status:

- **Implemented (all verified present on origin/main and spec-proven):**
  E0 contract (`model.spl`, `evidence_comparator.spl`), E1 red-team gates,
  E2/E2b/E3/E4/E7a-e format adapters
  (`src/lib/common/spec/evidence/format/{terminal_grid,text_protocol,
  binary_layout,scene_profile,simulation_profile,audio_profile,ml_profile,
  json_document}.spl` + `action_trace.spl`), E5 docgen evidence loader
  (`src/app/spipe_docgen/spipe_docgen/evidence_loader.spl`, wired into
  `generator.spl`, live regeneration gate green:
  `scripts/check/check-spipe-docgen-regeneration-live.shs`), E6 spec-to-SPipe
  bridge (`spipe_extension.spl`), E8 migration adapters (`legacy_facade.spl`,
  `untyped_capture.spl`), E9 docs/skills refresh. Core proof specs re-run
  green 2026-08-09: `typed_evidence_oracle_spec` 28/28,
  `terminal_grid_spec` 21/21, `exec_capture_spec` 6/6 (real processes).
- **Live vs fixture (the honest "mocking" ledger, updated 2026-08-09):** live
  capture now covers nearly every evidence domain. Provider modules:
  `exec_capture.spl` (real process), `file_capture.spl` (real file I/O).
  Live specs under `test/03_system/tools/spipe/examples/`:
  `live_terminal_capture_spec` (real subprocess stdout -> `TerminalSnapshot`),
  `live_json_capture_spec`, `live_text_protocol_capture_spec`,
  `live_binary_capture_spec` (real file round-trip -> PTE decode),
  `live_interactive_surface_spec` (real in-process widget-store mutations via
  `SgttiTestDriver.from_tui_state` -> real `WinTextSnapshot` rows + `ActionTrace`),
  `live_scene_capture_spec` (real `builder.label` -> `compute_layout` ->
  `widget_tree_to_draw_cmds` -> `DrawScene`, headless, no GPU),
  `live_simulation_capture_spec` (real `ChaosScheduler.pick_next` -> `TimelineEvent`),
  `live_audio_capture_spec` (real RIFF/WAVE bytes through the real `decode_wav`).
  Each carries a green/red/green sabotage proof and a hand-reasoned oracle —
  expected values are NEVER read from the evidence under test; that tautology was
  caught in review and rewritten twice, so check for it when reviewing a new lane.
  STILL FIXTURE-ONLY: `ml_profile` (blocked — `rt_torch_*` externs do not resolve
  under the interpreter runtime `bin/simple test` uses; see
  `doc/08_tracking/todo/live_ml_capture_blocked_2026-08-09.md`), 3D scene readback,
  and the three E8 reference manuals (which carry explicit honesty notes).
- **Open work:** (a) untyped-evidence migration backlog — 37 migrated + 159
  rejected of 1119 rows as of batch 10 plus the T4 NVMe cluster; sequential
  scanning is now yield-exhausted (batch 10 found 0 hits in 15+ sampled rows),
  see the backlog TODO's recommended change of approach
  (`doc/08_tracking/todo/untyped_evidence_migration_backlog_2026-08-08.md`);
  (b) live-capture infrastructure for the remaining domains
  (`doc/08_tracking/todo/sspec_live_capture_infrastructure_2026-08-08.md`);
  (c) all 2026-08-08/09 verification ran on the disclosed Rust SEED binary —
  a self-hosted redeploy + re-run gate is still owed. Plan for all three:
  `doc/03_plan/infra/sspec/modern_sspec_completion_plan_2026-08-09.md`.

## Load-bearing traps (from the comparator's own header, verify before trusting a new oracle)

1. **Observation is not an oracle.** Resolving evidence and printing it
   proves nothing; only a `compare_evidence` check against an `OracleSpec`
   is an assertion.
2. **Equality is not correctness.** A value can equal what a stale golden
   recorded without being right; oracles must be reasoned about, not just
   diffed.
3. **A pattern must be anchored to the full value.** `pattern_matches`
   matches the whole selected scalar — a substring pattern that merely
   matches a prefix or infix must fail, not pass.
4. **An ignore needs a reason.** An ignored check indistinguishable from "we
   never looked" defeats the whole point of a manifest; every ignore carries
   a stated reason.
5. **An all-ignore oracle is vacuous.** An `OracleSpec` where every check is
   ignored asserts nothing about the production system and must be treated
   as a red flag, not a pass.
6. **A closed oracle must reject undeclared fields.** An "open" document
   silently absorbs new fields with nobody deciding to allow them; a closed
   oracle mode must fail when evidence contains fields the spec didn't
   declare.
7. **A parse failure must not yield a silently-satisfied empty node set.**
   Zero resolved nodes must be a `cardinality_error`, not a green subset
   check.
8. **Manuals must carry spec+artifact hashes or they cannot be told from
   stale.** A `ManualBlock` with no hash of the spec that produced it and the
   artifact it describes cannot be distinguished from a manual regenerated
   against different evidence — treat an unhashed manual as untrusted.

## Verified repo facts (file:line, checked 2026-08-08)

- `ScenarioEvidenceArtifact` is **metadata-only** — `kind`, `title`, `mime`,
  `path`, `body`, `scenario_id`, `step_id`, `redacted`
  (`src/lib/common/spec/scenario_evidence.spl:44-52`). It carries no
  selector/oracle/comparison fields; the typed-evidence model above is a
  separate, newer layer, not an extension of this struct.
- The existing snapshot comparator (`compare_snapshots`) is **trim + exact**:
  it trims both sides (`src/compiler_rust/lib/std/src/spec/snapshot/comparison.spl:37`)
  then does a line-by-line Myers-style diff whose only ops are `Delete`/
  `Insert`/`Equal` (`:98-127`) — no line-level fuzzy match, no anchored
  pattern classes. This is the pre-existing baseline the typed-evidence
  comparator's anchored-pattern and cardinality rules improve on.
- The old `Capture` trait had a `render_md(audience: Audience) -> text`
  method directly on the capture object
  (`doc/05_design/sspec_capture_extension.md:35-42`). This **cannot work**
  across the capture-runtime/docgen process split: docgen never holds a live
  runtime object to call `render_md()` on. This is the concrete reason
  `model.spl` deliberately holds no rendering code and instead emits generic
  `ManualBlock` records for docgen to render.
- PTE bitfield ground truth used as a `binary_field`/`bit_range` selector
  worked example, in `src/os/kernel/types/bitfield.spl`: bit 0 = present,
  bit 1 = writable, bit 2 = user, bits 51:12 = physical address, bit 63 = NX
  (`pte_get_present`/`pte_set_present` etc. at lines 72-113). Concretely,
  `pte_make(0x1234_5000, true, true, false, true) ==
  0x8000_0000_1234_5003` (present + writable set, user clear, NX set, phys
  addr `0x1234_5000`) — use this as the canonical worked example when writing
  a `bit_range`/`binary_field` selector spec against a real PTE value.

## What landed since (2026-08-08, untyped-evidence migration lane, E8)

- Legacy-migration sub-lane (moving existing loose-text specs onto the typed
  pipeline additively) is live and bounded: candidate population enumerated
  once via `scripts/check/scan-untyped-evidence-candidates.shs` at 1119
  category-1 rows across 414 files (doc:
  [doc/08_tracking/audit/untyped_evidence_migration_candidates_2026-08-08.md](../../../08_tracking/audit/untyped_evidence_migration_candidates_2026-08-08.md)).
  Progress as of the 8th worked batch: 30 rows migrated ("yes"), 135
  explicitly rejected with a recorded one-line reason each (numeric-only,
  in-memory, static `file_read` source-text, or duplicate) — the rest remain
  unmarked "no" (not yet triaged). Triage rule and worked examples:
  [doc/05_design/infra/sspec/untyped_evidence_migration_design.md](../../../05_design/infra/sspec/untyped_evidence_migration_design.md),
  [doc/07_guide/infra/sspec_legacy_migration.md](../../../07_guide/infra/sspec_legacy_migration.md).
  Tracked backlog with resume instructions:
  [doc/08_tracking/todo/untyped_evidence_migration_backlog_2026-08-08.md](../../../08_tracking/todo/untyped_evidence_migration_backlog_2026-08-08.md).
- Yield rate on unmigrated rows has fallen sharply batch over batch (roughly
  5/8 → 1/24 → 0/26 → 1/41 accepted) as the easy front-loaded category-1 wins
  are exhausted; most of the remaining population is the scanner's known
  false-positive class (a spec `file_read`s its own source and asserts on the
  literal text — a static-authorship check, not a live-system observation,
  explicitly out of scope per the design doc). This lane has no natural
  single-session completion point at the current per-batch rate.
- A companion, unstarted lane — real live-capture infrastructure per domain
  (TUI/GUI action trace/2D-3D scene/simulation/audio/ML) so `format/*.spl`
  adapters stop taking only constructed fixture input — is tracked separately
  and explicitly scoped as multi-session research+design+implement work, not
  a bounded backlog like the migration above:
  [doc/08_tracking/todo/sspec_live_capture_infrastructure_2026-08-08.md](../../../08_tracking/todo/sspec_live_capture_infrastructure_2026-08-08.md).
- Shared-tree operating note for anyone resuming this lane: the migration
  candidate audit doc and backlog TODO are hot-contended files edited by many
  concurrent batches. When landing a batch's changes, diff its final doc
  version against the row set it actually started from and apply only the
  rows it newly touched onto a freshly-fetched `origin/main` copy — never
  push a batch's full doc blob wholesale, since a batch that started from a
  stale local snapshot will otherwise silently drop rows another batch
  already landed.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release
artifacts for Modern SSpec typed evidence — especially when an E2-E9 wave
lands — update this skill with the new links and current handoff notes.
Update the "what landed" vs "what is design-only" split FIRST, since that is
the fact most likely to go stale.

## Update Checklist

- Add links to new or changed requirements, architecture, design, plans,
  specs, and reports.
- Record affected layers and link their layer expert skills.
- Record implementation constraints, known blockers, and required
  verification commands.
- Update this file after each pipeline stage before handing off to the next
  stage.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
