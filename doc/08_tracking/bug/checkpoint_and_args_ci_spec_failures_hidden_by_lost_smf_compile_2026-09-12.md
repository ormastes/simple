# Three runner specs were silently losing their examples to a hard SMF compile failure

- Status: OPEN (2026-09-12)
- Area: app/test_runner_new specs; compiler / SMF lowering
- Severity: medium (real red hidden behind a file-level compile error; no false green,
  but 12 examples were never executed in any directory run)
- Found by: RUNNER-DEGRADE lane, as a side effect of making hard SMF-compile failures
  degrade to the interpreter. Not fixed here — the degrade is the fix for the
  *invisibility*; the assertions these specs now run are a separate matter.

## What changed and what it revealed

`bin/simple test test/01_unit/app/test_runner_new/` before and after the degrade fix
(seed sha256 `3d120a6f`, same worktree, same binary, only `src/**` changed):

| spec | before | after |
|---|---|---|
| `bdd_step_marker_spec.spl` | `executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=parse-error` | `outcome=OK executed=3 passed=3 failed=0` |
| `checkpoint_spec.spl` | `outcome=ERROR executed=1 passed=0 failed=1` | `outcome=ERROR executed=8 passed=4 failed=4` |
| `test_runner_args_ci_spec.spl` | `outcome=ERROR executed=1 passed=0 failed=1` | `outcome=ERROR executed=5 passed=4 failed=1` |

Every other file in that directory is byte-identical apart from the new trailing
`degraded=` token. Suite totals: executed 220 -> 243, passed 202 -> 216, failed 19 -> 27.
The failed count RISES because hidden failures became visible, not because anything
regressed.

Two things need separate follow-up and neither is in this lane's scope:

1. **`checkpoint_spec.spl` has 4 genuinely failing examples** that no directory run has
   executed until today. They must be triaged on their merits.
2. **`bdd_step_marker_spec.spl`'s old `reason=parse-error` was a misclassification.** The
   file parses fine; its SMF compile failed, and the runner's load-failure classifier read
   that as a parse error. Any sweep that trusted `reason=parse-error` was told the wrong
   thing about this file.

## The compile errors themselves

`checkpoint_spec.spl` fails with `Undefined("undefined identifier: to_int")` on the SMF
lowering path while running fine under the interpreter. That is the same class as
`doc/08_tracking/bug/macro_contracts_module_unresolvable_in_compiled_spec_lane_2026-09-12.md`
and the devhub `print_raw` record: a name the interpreter resolves and the self-hosted HIR
lowering does not. `to_int` is a core text method, so the gap is wider than the two symbols
already filed.

## Repro

```
bin/simple test test/01_unit/app/test_runner_new/checkpoint_spec.spl   # single file: interpreter, 8 examples
bin/simple test test/01_unit/app/test_runner_new/                      # directory: compiled lane
```
Read the `degraded=` token on the directory run's `SPEC FILE VERDICT:` line for the cause.
