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

## SSpec count-truthfulness lane handoff — 2026-08-16

The count gate implementation now admits the selected runner through the
canonical self-hosted guard and preserves a nonzero runner result. Its focused
modern system contract is
[`test/03_system/infra/sspec_count_truthfulness_spec.spl`](../../../../test/03_system/infra/sspec_count_truthfulness_spec.spl),
with the Markdown-only
[`doc/06_spec` mirror](../../../06_spec/03_system/infra/sspec_count_truthfulness_spec.md),
[`system test plan`](../../../03_plan/sys_test/sspec_count_truthfulness.md),
[`operator guidance`](../../../07_guide/infra/sspec_scenario_manual.md), and
[`tracking record`](../../../08_tracking/todo/check_scripts_seed_identity_fail_open_2026-07-28.md).
The production owner remains
[`scripts/check/check-sspec-count-truthful.shs`](../../../../scripts/check/check-sspec-count-truthful.shs).

Frozen contract: `run_count_truthfulness_guard` drives visible `step("...")`
flows for qualified-runner selection, a two-example positive fixture, an
anchored-count edge fixture, a deliberately failing runner, and a missing
compiler path. `REQ-SCT-001` covers identity admission, `REQ-SCT-002` covers
runner-exit preservation, and `REQ-SCT-003` covers exact declared/reported
equality. New assertions use built-in matchers and must remain real positive,
edge, and error oracles; placeholder passes and executable `.spl` mirrors under
`doc/06_spec` are forbidden.

Evidence status is **TEST_BLOCKED**: this worktree has no current-source
admitted pure-Simple CLI. Do not use the Rust bootstrap seed, a stale binary,
or a skipped run as PASS evidence. Once a qualified environment exists, run the
system spec, `spipe-docgen`, and `sspec-maintain` with that same admitted CLI,
then update the lane state and manual provenance from the retained results.

## Documentization score: the measured 90+ recipe and the seed-lane measurement (2026-09-05)

The scorer (`src/app/sspec_maintain/`) is now documented rule-by-rule, with the
exact token each `SSDOC-*` rule reads and the aggregate cost of each miss, in
[`.claude/skills/spipe.md` § "Scoring 90+"](../../../../.claude/skills/spipe.md).
Read that section before writing or converting any `*_spec.spl`; the scaffold
`.claude/templates/spipe_template.spl` already carries the score-bearing shape.

- **Two surfaces.** GATE = `analyze_sspec_text` (what `bin/simple test` enforces,
  min 80 via `src/app/test_runner_new/sspec_score_gate.spl`); SCAN =
  `analyze_sspec_pair_text` + lifecycle links (what `sspec-maintain scan`
  reports) — SCAN is 2.5 lower with no `doc/06_spec` mirror (MNT-002). Target SCAN.
- **Measured worked example:** `build/nb/fixtures/worked_example_spec.spl` (the
  text in the skill) = GATE 100 / SCAN 97. Calibration fixtures predicted from
  the source matched to the point (75, 49, 49, 100).
- **Measurement on a bootstrap-only host:**
  `sh scripts/check/sspec-score-seed-lane.shs <spec|dir>` — runs the real
  scorer modules (whitespace/comment-only reshaped copies, proven by residue
  hash, three named runtime-extern deltas) under the Rust seed. Why nothing
  else works here:
  [`doc/08_tracking/bug/phase2_native_build_hello_world_invalid_heap_and_scorer_segv_2026-09-05.md`](../../../08_tracking/bug/phase2_native_build_hello_world_invalid_heap_and_scorer_segv_2026-09-05.md),
  [`doc/08_tracking/bug/rust_seed_parser_behind_main_grammar_blocks_simple_test_2026-09-05.md`](../../../08_tracking/bug/rust_seed_parser_behind_main_grammar_blocks_simple_test_2026-09-05.md).
- **Scorer fixes landed the same day** (`source_facts.spl`): ORA-002 no longer
  exempts `var` (reassigned bindings are excluded instead), a trailing comment
  no longer hides a tautology, `# evidence(...)` prose no longer counts as a
  capture (only `# @capture` / `.evidence.sdn` do on comment lines), MNT-009
  strips sentence punctuation. Record + specs:
  [`doc/08_tracking/bug/sspec_scorer_loopholes_var_tautology_comment_evidence_2026-09-05.md`](../../../08_tracking/bug/sspec_scorer_loopholes_var_tautology_comment_evidence_2026-09-05.md),
  `test/01_unit/app/sspec_maintain/scorer_loopholes_spec.spl`,
  `test/01_unit/app/sspec_maintain/scorer_loopholes_adjacent_spec.spl`.
- **Lane-gated skips stopped capping SKIP-clean specs at 49 (2026-09-06,
  `source_facts.spl`).** `_is_pending` flagged every `skip(...)` call, so a spec
  that probes an absent lane (GPU, board, QEMU) and reports the documented
  `skip:` outcome tripped ORA-001 — a rule whose own evidence text says
  *unconditional* scaffold. A `skip(...)` reached only through an `if`/`elif`/
  `else:` branch inside a scenario is now exempt; every other marker, an
  unguarded `skip(...)`, and `real_assertion_count == 0` still fire.
  Measured on `test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl`:
  49/100 with 1 blocker → 84/100 with 0. Specs:
  `test/01_unit/app/sspec_maintain/pending_detection_spec.spl`.
- **Not changed, deliberately:** MNT-002 (mirror) and MNT-007 (lifecycle links)
  together cost at most 3.5 aggregate on SCAN and are true statements about the
  spec; a 90 is reachable with both outstanding, so neither rule was weakened.

## Training loop + plugin arch (2026-09-05, later session)

- **The checklist, not the model, decides the score.** Controlled: same model
  (haiku), same low effort, three specs each — old `≥80` checklist gave
  **84/78/78 (all fail)**; rewritten `≥90` checklist gave **90/95/90 (all pass)**.
  A second batch on sonnet, including a blocker file, went **49→90** and
  90/90/90/90 in one iteration each, with the checklist reported sufficient.
  Checklist: `doc/00_llm_process/spipe/skill.md` § "Modern SSpec Score ≥ 90".
- **The one rule that decides everything:** clear every finding EXCEPT the five
  mirror-only IDs (`MNT-002/005/008`, `EVD-002/003`) and you land on exactly 90.
  `EVD-001` and `MNT-001/003/004/006/007/009` are source-fixable but share a
  dimension with mirror rules, so workers mistake them for unfixable and stop at
  84. Worked example: `balance_score_spec.spl` had ZERO NAR/BEH/ORA/TRC/COV
  findings and still scored 84 (EVD-001 ×3 + MNT-001).
- **`# @req` placement is worth 38 points.** Above the `it` line → `TRC-003`
  blocker → 49. Inside the `it` body → 87. Proven with a one-line diff.
- **Scorer is now plugin architecture.** `dimensions.spl` holds the dimension
  weights, blocker cap and release target as DATA; `analyzer.spl` holds 24
  per-rule `_detect_*` functions behind `sspec_source_detectors()` /
  `sspec_manual_detectors()`; `registry.spl` unions the rule_ids.
  **Adding a scoring algorithm = one detector fn + one registry row** — no
  dispatcher and no weight literal to edit. Refactor parity was byte-identical.
  Bidirectional coverage is pinned by
  `test/01_unit/app/sspec_maintain/detector_registry_coverage_spec.spl`.
  **Any new scorer module must also be added to the hardcoded module list in
  `scripts/check/sspec-score-seed-lane.shs`** — omitting it broke that lane.
- **Measurement tool:** `sh scripts/check/sspec-train.shs <dir>` scores a tree and
  prints a **per-rule histogram** (which rule costs the most points), fail-closed
  (0 specs scanned = exit 2). Use it to find which rule the checklist is still
  failing to convey — a rule that keeps firing across batches is a checklist
  defect, not a spec defect.
- **The MNT-002 "-2.5" figure above understates the real penalty, and that is a
  filed bug.** `scan` charges MNT-005/MNT-008/EVD-002/EVD-003 even when NO mirror
  file exists, penalising one absence five times (~7 aggregate points, not 2.5).
  Root cause: `src/app/sspec_maintain/main.spl` reads the mirror with `file_read`,
  which swallows a missing-file `Err` into `""`, so the analyzer receives
  `Some("")` = "stale but present" instead of `None`. The seed lane implements the
  documented contract and scores the same spec **97**. Filed, with two RED specs,
  deliberately NOT fixed — a fix shifts every score in the repo:
  [`doc/08_tracking/bug/sspec_scan_manual_findings_fire_without_mirror_2026-09-05.md`](../../../08_tracking/bug/sspec_scan_manual_findings_fire_without_mirror_2026-09-05.md).

## Known limitation of the current loop (2026-09-05, honest, not hedged)

The training loop above (checklist -> low-effort worker -> `sh
scripts/check/sspec-train.shs` score -> edit the checklist -> re-score on the
*same* specs) is the shape flagged as a "wrong flywheel" in
`doc/01_research/infra/spipe/spipe_skill_foundry_debug_training.md` §30: a loop
that scores work, edits the guidance from the score, then re-scores with that
same guidance can raise its own numbers without raising capability.

The honest split, reconstructed from commit timestamps rather than memory — the
loop did better than a pure flywheel, and worse than a clean experiment:

- **Held-out: 14 of 21 specs.** The checklist was rewritten at 13:50 from
  round-1 evidence on three files. Round 2 (3 specs), the sonnet batch (4), the
  blocker batch (3) and the final near-target batch (4) were all scored *after*
  that, on files the checklist had never been tuned against. All 14 reached
  >=90. That is genuine transfer evidence.
- **Same-case: 7 of 21.** The three round-1 leftovers were the exact files whose
  failure motivated the rewrite. The four-spec batch that stalled at 84/84/84/88
  triggered the 14:00 ORA-003 edit and was then re-run against it. Those seven
  only show the checklist can be tuned until a known file passes — the flywheel
  failure itself — and should not be counted as capability.

So the defensible claim is **14/14 on held-out specs**, not 21/21.

**Now standing, not retrospective (2026-09-05, same day).** The three gaps
this section used to flag are closed:

- **Standing held-out partition:** `.spipe/training/splits.sdn` records all
  21 specs with `split` = `train` (the 7 same-case files: the 3 round-1
  files whose 84/78/70 evidence motivated the rewrite — `balance_score_spec`,
  `admission_verdict_spec`, `graph_source_spec` — plus the 4 that stalled at
  84/84/84/88 and triggered the 14:00 ORA-003 edit —
  `diagnostics_registry_spec`, `graph_source_v2_spec`, `link_extraction_spec`,
  `search_adapter_spec`) or `private_test` (the 14 held-out files: round 2 +
  the sonnet batch, the blocker batch, and the final near-target batch). File
  list and derivation method (git log on the checklist commits `bf9cd7b`/
  `3db4e4e` in `.spipe/spipe`, cross-checked against every landing commit's
  own score table) are recorded in the splits file's header — no per-spec
  list existed in prose before this.
- **Leak checks:** `sh scripts/check/sspec-train.shs --split <name>` reads
  the splits file and, before scoring a non-`train` split, fail-closed ERRORs
  (exit 2) if (a) a fresh sha256 of the checklist file no longer equals the
  `checklist_digest` frozen in the splits file, or (b) any selected spec's
  path is cited verbatim in the checklist file. Gate (a) went through one
  correction the same day: an earlier cut compared each held-out spec's OWN
  git timestamp against a freeze cutoff, which is backwards — fixing a
  held-out spec to reach target necessarily edits it after the freeze; that
  is the training step, not a leak. The direction that actually matters is
  the CHECKLIST changing after it saw a held-out spec's findings, which is
  what the digest gate now checks. It proves the checklist text is
  byte-identical to the one frozen at commit `3db4e4e`; it does **not**
  prove the 14 held-out specs were unseen when `3db4e4e` was written — that
  provenance claim still rests on the `bf9cd7b`/`3db4e4e` commit-timestamp
  argument above, which is unenforced by any mechanism.
- **Same-case exclusion:** built into the split itself — `--split train`
  only ever scores the 7 tuned-on files, `--split private_test` only the 14
  that were never used to write the checklist. Both gates above are skipped
  for `train` on purpose (see the script header): gating deliberately
  tuned-on rows would make ordinary train scoring ERROR every time the
  checklist is legitimately edited.

**Measured results (checklist read via `SIMPLE_SSPEC_CHECKLIST` pointed at
the `.spipe/spipe` submodule checkout, since it is uninitialized in the
sparse worktree this was run from):**

```
sspec-train.shs: PASS — 7 fixture(s) checked (selftest only, no real scan requested)
sspec-train.shs: PASS — 14 checked, split=private_test, target=90
sspec-train.shs: PASS — 7 checked, split=train, target=90
```

Unlike the earlier (backwards) temporal gate, `--split private_test` now
passes cleanly: the checklist at `.spipe/spipe/doc/00_llm_process/spipe/skill.md`
hashes to `dd830096...` — the content at SPipe `06d7d34`, which is `3db4e4e`
rebased onto SPipe origin/main and pushed, and which the outer repo's
`.spipe/spipe` gitlink now pins (the first freeze, `deaf594d...`, was against
a `3db4e4e` that existed only locally; a fresh clone would have ERRORed — see
the re-freeze note in the splits file header). Gate (a) clears, and
none of the 14 held-out paths are cited in it, so gate (b) clears too. Read
this PASS for exactly what it proves and no more: the checklist has not
drifted since the split was frozen, and no held-out spec is named in it —
**not** that the 14 specs were unseen when that checklist text was written.
That second claim is still the retrospective commit-timestamp argument two
sections up, unenforced by any mechanism; a future loop revision that wants
a mechanically-verified version of it needs to freeze the held-out set
*before* scoring, and record that freeze moment independently of the
checklist's own content. See `.claude/skills/lib/debug_ladder.md`
"Anti-flywheel rules" for the general counter-rules this mechanism
implements.

## Lane docs (2026-09-05)
- design: `doc/05_design/infra/sspec/sspec_training_heldout_gate_design.md` · plan: `doc/03_plan/infra/sspec/sspec_training_heldout_gate_plan.md` · state: `.spipe/sspec_training_heldout_gate/state.md`
