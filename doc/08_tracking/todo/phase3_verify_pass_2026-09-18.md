# Phase-3 todo-ledger verify pass — 2026-09-18

Full-tree verification of every `open` row in `doc/08_tracking/todo/todo_db.sdn`
at origin/main, per the restart-plan procedure (same pipeline as the phase-2
bug-ledger pass).

## Census

- 173 open rows exported, 173 verdicts, coverage check: 0 missing, 0 duplicate.
- Verify: 7 parallel agents, read-only against origin/main.
- Review: 2 independent reviewers over all 32 closure verdicts — **all 32 confirmed**.

## Outcome (applied in this commit)

- 32 rows -> `closed` (27 work-done, 4 superseded/mirror-stale, 1 not project-owned).
- 141 rows remain `open`, each with fresh liveness evidence in the verdict files.

## Notable closures

- Rows 109-136: `compiler_interpreter_integration_spec` mirror stubs superseded
  by the todofix-wave real subprocess e2e specs (four are intentional RED pins
  for undelivered features, each carrying its own bug-doc NOTE).
- Row 37: vendored upstream shlex doc — not project-owned work per the
  Owned-Code Scope.
- Rows 176/178/311/315: landed work with cited commits/specs (dynamic pass
  routing, async timer wakeup, Vulkan mask-plane spec, readback counter).
- Rows 137/138/158/318: mirror-tree or duplicate rows superseded by canonical
  live rows.

## Remaining backlog

141 open rows: mostly spec placeholders awaiting real implementations
(SSR/hydration, structural diff, set operators in specs, native perf harnesses),
extern-gated GPU provider-honesty markers, and blocked infrastructure items
(sosix resume conditions, self-hosted-binary-gated reruns). Evidence per row is
on file in the phase-3 verdict bundle.
