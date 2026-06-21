# Recent Plan Cleanup Guide

Use this guide when a cleanup task asks to find recent unfinished
`doc/03_plan/**/*.md` work, mark completed plans done, and leave unfinished
plans restartable.

## Scope

Start from the user-provided exclusions. The 2026-06-18 cleanup lane excluded
GPU web/DB offload and plans whose only remaining work was unavailable external
platform proof such as macOS Metal, Windows DirectX, ROCm/HIP, BSD, QEMU, FPGA,
board, or other host-only evidence.

Do not implement every unfinished product feature as part of the cleanup. The
cleanup deliverable is a reliable classification matrix, evidence-backed done
marks, and concrete next closure actions for unfinished work.

## Workflow

1. Create or update the SPipe state file under `.spipe/<cleanup-name>/state.md`
   with acceptance criteria.
2. Create or update the plan under `doc/03_plan/agent_tasks/`.
3. Discover candidates with a dated query and record the query in the plan.
4. Split plan/research review across disjoint lower-model lanes when available,
   usually Codex Spark, Claude Haiku, or Claude Sonnet for compiler, runtime,
   and app/UI. Add review-discovered waves when normal review finds omissions.
5. Use only these final states:
   - `mark-done`
   - `needs-evidence`
   - `needs-requirement-selection`
   - `needs-implementation`
   - `superseded/merge`
6. Require normal/highest-capability LLM review before accepting done marks,
   merged lower-model findings, or broad exclusions.
7. Run the generated-spec layout guard and SPipe command wiring check before
   handoff.
8. Commit only the cleanup lane files. Preserve unrelated dirty worktree files.

## Evidence Rules

Only use `mark-done` when the row names concrete evidence for implementation,
focused tests/specs, generated/manual docs, requirements or traceability, guide
applicability, and remaining follow-up state. If any of those are missing, keep
the row open and name the smallest next closure action.

Use `needs-evidence` when implementation appears present but proof is too
narrow or missing. Use `needs-requirement-selection` when final requirement or
NFR artifacts are missing. Use `needs-implementation` when product behavior or
test/spec fixes remain. Use `superseded/merge` only with the replacement plan or
explicit exclusion target named in the row.

## Required Guards

Run these before handoff:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
sh scripts/setup/install-spipe-dev-command.shs --check
```

The first command must print `0`. The second command should print
`STATUS: PASS spipe-dev-command wiring`; otherwise log the failure in the
SPipe state file.

## Current Example

The current cleanup matrix is:

- `doc/03_plan/agent_tasks/recent_unfinished_plan_cleanup.md`
- `.spipe/recent-plan-cleanup/state.md`

Those files are the restart source for the 2026-06-18 cleanup lane.
