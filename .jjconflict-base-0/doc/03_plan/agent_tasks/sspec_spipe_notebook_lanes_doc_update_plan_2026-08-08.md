# SSpec/SPipe Skill + Doc Update for Notebook Lanes — Small-Agent Parallel Plan

**Date:** 2026-08-08
**Status:** Plan (paths verified by repo scan 2026-08-08)
**Sources:** `doc/01_research/app/tools/notebook_lanes_research.md`,
`doc/05_design/app/tools/notebook_lanes_architecture.md`,
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`
**Knowledge hub:** `doc/00_llm_process/feature_expert/notebook_lanes/skill.md` (exists; the
single source each task links back to — do NOT duplicate its content, link it).

## Execution model — small agents + higher-model review

- Every task below is sized for a **haiku** agent: one file (or one small file set), a
  verbatim source section to draw from, and a mechanical verify command.
- **Review gate (mandatory):** every haiku result is reviewed by a **sonnet** agent
  (diff review: correct paths, no invented symbols, links resolve); sonnet escalates
  disputed items to the session model (Fable). Per standing rule
  `feedback_review_every_subagent_result_with_higher_model`: send the ORIGINAL lane back
  with guidance for rework — don't patch over it.
- Docs-only change set (no `src/**` behavior changes except D-stream notes); safe to run
  all streams in parallel. Rule: link to `feature_expert/notebook_lanes/skill.md`, don't
  copy design prose.

## Stream S — SPipe skill (`.claude/skills/`)

**S1. `.claude/skills/spipe.md` — add notebook-lane section** `[haiku]`
Add a short "Notebook lanes" subsection to the lane list: `%mode`/`%%mode` magics reuse
the composite spec grammar verbatim; `NotebookExecutor` trait is the session seam; lane
probing wording (`available`/`skip:`/`blocked:`) is shared with the test runner. Link the
feature_expert skill and `doc/07_guide/app/tools/jupyter.md`.
Verify: links resolve (`ls` each target); section ≤40 lines.

**S2. `.claude/skills/lib/spipe_notebook.md` — new sub-skill** `[haiku]`
Model on `.claude/skills/lib/spipe_ui.md` (closest analogue). Content: writing specs for
notebook sessions (session lifecycle, cell-delta execution, magics parsing, lane locks),
which test tier each belongs to (`test/01_unit/lib/notebook/`, `test/03_system/jupyter/`).
Verify: referenced from spipe.md (S1 adds the link); follows spipe_ui.md structure.

**S3. `.claude/templates/spipe_template.spl` — notebook-lane scaffold note** `[haiku]`
Add a commented variant block (or sibling `spipe_notebook_template.spl` only if a comment
block can't express it) showing a lane-gated spec skeleton (probe → skip-clean → execute).
Verify: template still parses (`bin/simple lint` on the template if lintable, else parse
by scaffolding once to scratch).

**S4. `.claude/agents/spipe/{dev,spec,implement,verify}.md` — lane awareness** `[haiku]`
One paragraph each: notebook-lane tasks exist; specs must be SKIP-clean without
QEMU/CUDA/Vulkan; link the feature_expert skill.
Verify: grep `notebook_lanes` hits all four files.

## Stream G — Guides (`doc/07_guide/`)

**G1. `doc/07_guide/infra/sspec_scenario_manual.md` — lane-gated notebook specs** `[haiku]`
Add the notebook-lane spec pattern: host-aware probing, `skip:`/`blocked:` wording, the
interrupt-contract assertion pattern (§6.3 of the design).
Verify: doc link check on the section.

**G2. `doc/07_guide/infra/sspec_antipatterns.md` — new antipatterns** `[haiku]`
Add: (a) asserting cross-lane state in `%%mode` cells (explicitly unsupported),
(b) hard-failing when a lane is absent instead of SKIP-clean, (c) testing accumulation
internals instead of the `NotebookExecutor` contract.
Verify: three entries, each with a wrong/right example.

**G3. `doc/07_guide/app/tools/jupyter.md` — modes/magics/labextension** `[haiku]`
This is plan task E1 of the notebook plan; do the doc skeleton now (modes table, magics
list, `%lanes` sample marked ILLUSTRATIVE until implementation lands) so sspec authors
have a target. Also add cross-link from `doc/07_guide/app/spipe/scenario_manual_example.md`.
Verify: `%lanes` sample carries the ILLUSTRATIVE marker; links resolve.

**G4. `doc/07_guide/infra/testing.md` + `test_layout_traceability.md`** `[haiku]`
Register the new test locations (`test/01_unit/lib/notebook/`, extended
`test/03_system/jupyter/`) and their lane gating in the layout/traceability tables.
Verify: table rows added; paths match the notebook plan's verify commands.

## Stream K — Knowledge (`doc/00_llm_process/`)

**K1. `feature_expert/notebook_lanes/skill.md` — refresh** `[sonnet]`
Already modified in the working copy (see git status) — reconcile, don't clobber: diff WC
vs HEAD first (`feedback_diff_wc_against_head_before_blaming_source`). Fold in the final
research/design/plan doc paths and the trait/magics summary.
Verify: `git diff` shows forward-only delta; all doc links resolve.

**K2. `layer_expert/test_runner/skill.md` — lane-lock note** `[haiku]`
Line ~185 already links notebook_lanes; add one line: lane locks
(`src/lib/nogc_sync_mut/notebook/lane_locks.spl`, planned H2) will be shared with the
runner's GPU lanes — mark PLANNED.
Verify: PLANNED marker present (no claim the module exists yet).

## Stream D — sspec/spipe tooling notes (report-only, no code)

**D1. `src/app/sspec_maintain/` rule note** `[haiku]`
File a TODO doc entry (not code) in `doc/08_tracking/todo/` via `bin/simple todo-scan`
conventions: sspec-maintain rules should recognize lane-gated notebook specs so SKIP-clean
lanes don't score as missing coverage. No `src/**` edit in this plan.
Verify: entry appears after `bin/simple todo-scan`.

**D2. `src/app/spipe_docgen/` lane rendering note** `[haiku]`
Same mechanism: docgen should render per-cell `%%mode` lane badges when notebook specs
land. Generate to scratch first (`reference_spipe_docgen_regenerates_doc_06_spec_manuals`).
Verify: TODO entry present; no `doc/06_spec/` files touched.

## Stream R — further research (feeds later revisions, non-blocking)

**R1. Jupyter protocol 5.x deltas** `[haiku]` — confirm control-channel interrupt +
comm lifecycle details against the wire-protocol docs; write findings into the research
doc's references section.
**R2. jupyterlab-lsp + galata current APIs** `[haiku]` — verify the extension-stream
assumptions (X2/X3 of the notebook plan); note version pins.
Review: sonnet checks claims against fetched sources, not memory.

## Schedule (parallel, 3 small agents + 1 reviewer)

| Slot | Agent A (haiku) | Agent B (haiku) | Agent C (haiku) | Reviewer (sonnet→Fable) |
|---|---|---|---|---|
| 1 | S1 → S2 | G1 → G2 | K2, R1 | review slot-1 outputs |
| 2 | S3 → S4 | G3 → G4 | D1 → D2, R2 | review slot-2 outputs |
| 3 | — | — | — | K1 (sonnet) + final link sweep |

Final gate: one sonnet pass runs a repo-wide link check over every touched doc and greps
for invented paths/symbols; failures go back to the original lane for rework.
