# Bootstrap keep-going policy verification — 2026-09-30

## Scope

Worktree: `D:/wk-bootstrap-keep-going-20260930`.

Host native-build and bootstrap runs collect independent failures by default.
`CI=true` or `CI=1` selects fail fast unless overridden. Explicit
`SIMPLE_COMPILE_FAIL_FAST=0|1` overrides that default; ordered `--keep-going` and
`--fail-fast` flags override the environment, with the last flag winning.
Empty or invalid environment values use the CI/host default.

The phase matrix retains failures, records unlaunched work as `SKIPPED`, and
exits nonzero even when later work succeeds. Snapshot/admission prerequisites
remain fatal. Compatible caches and the bounded 200-module worker poison budget
remain intact. The supervisor cancels concurrent work after qualification
failure only under the resolved fail-fast policy.

## Executed verification

Three focused verification cycles were completed. Earlier passes were rerun
only after concrete policy or test changes; no further test cycle was run after
the final native-build help clarification.

| Command/check | Result | Evidence scope |
| --- | --- | --- |
| `sh scripts/check/check-bootstrap-keep-going-policy.shs` | PASS, final cycle | Executes production matrix orchestration, inventory orchestration, terminal verdict, and supervisor cancellation branch with fake commands. Checks host/CI defaults, explicit environment values, ordered flags, child inheritance, later host execution, fail-fast skipped rows, unsupported prerequisite latch, nonzero aggregate failure, retained cache content, and fatal invalid snapshot admission. |
| `sh scripts/check/check-bootstrap-phase-collect-failures.shs` | PASS, final cycle | Normal/full strategies collect independent failures, enforce artifact prerequisites, and retain aggregate failure. |
| `sh -n scripts/bootstrap/bootstrap-cache-policy.shs scripts/bootstrap/bootstrap-from-scratch.sh scripts/bootstrap/bootstrap-strategy.shs scripts/bootstrap/bootstrap-phase-verification.shs scripts/check/check-bootstrap-keep-going-policy.shs` | PASS, second cycle | Shell syntax of the then-current policy, entrypoint, supervisor, phase verifier, and regression. Subsequent test refinements were executed successfully in the final cycle. |
| Scoped `git diff --check` covering this lane's source, scripts, CI workflows, documentation, skill guidance, and modified fixtures | PASS, final cycle | No whitespace errors in the reviewed policy lane changes at that point. |

## Unexecuted checks and limits

- No expensive bootstrap or native compiler build was run.
- The Simple policy helper, CompileContext integration, and native CLI changes
  have not been qualified by a native execution in this lane.
- Full compiler/library/MCP checks and runtime smoke gates were not run here.
- Existing collection fixtures were updated to explicitly select collect-all
  or load the new helper when extracting production functions. Apart from the
  phase collection regression listed above, those fixtures were not executed
  in this lane.
- The fake-command regression proves shell scheduling and policy behavior;
  it does not establish native worker recovery or HIR cache correctness.
- No release readiness PASS is claimed. No commits or publication occurred.

The final help-only correction clarifies that collect-all is the host default
and CI defaults to fail fast. Tests were not rerun after that wording change,
in accordance with the three-cycle limit.
