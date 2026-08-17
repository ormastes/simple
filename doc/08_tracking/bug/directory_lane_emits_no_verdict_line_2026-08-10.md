# Directory test lane emitted no `SPEC FILE VERDICT:` line for any file

- **Filed:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Related:** `0ff267a366a` (single-file half), `unrun_spec_emits_no_verdict_line_2026-08-10`,
  `killed_spec_emits_no_verdict_line_2026-08-09`

## Symptom

`bin/simple test test/01_unit/lib/blink` ran 24 files, exited 1, and emitted
**zero** `SPEC FILE VERDICT:` lines — for passing files as well as broken ones.
The same specs run one at a time emitted the line correctly.

Measured on the pre-fix tree (Rust bootstrap seed, `bin/simple --version`
self-reports seed):

| lane | files | exit | `SPEC FILE VERDICT` lines |
|---|---|---|---|
| `bin/simple test test/01_unit/lib/blink/paint_tree_walker_spec.spl` | 1 | 1 | **1** (`reason=unresolved-module`) |
| `bin/simple test test/01_unit/lib/blink` | 24 | 1 | **0** |

Because the render-lane sweep counts verdict lines rather than exit codes, an
entire directory read as "not yet run". That is the mechanism by which 24
missing blink modules stayed invisible for weeks. The exit code was never the
fail-open — it was correct (1) in every case.

## Root cause

Two lanes, one of which never emitted verdicts at all.

- `src/app/test_runner_new/test_runner_single.spl` runs ONE file, owns the
  `real_executed == 0` branch, and — since `0ff267a366a` — emits
  `unrun_verdict_line()` there.
- `src/app/test_runner_new/test_runner_main.spl` aggregates: it builds
  `TestFileResult` records and prints its own `PASS`/`FAIL <path> (n passed,
  m failed)` summary lines via `std.test_runner.test_runner_output`. It never
  reaches `test_runner_single`'s zero-executed branch, and it never printed a
  verdict line for **any** outcome.

`0ff267a366a` could not have closed this. Its author diagnosed the problem as
*"an unloadable spec is misclassified"* and fixed the classification. The
actual defect in the aggregating lane is one level up: that lane emitted no
verdict lines whatsoever, so there was no classification to correct. A
single-file reproduction — which is how the fix was verified — is structurally
incapable of exercising the aggregating lane.

## Fix

One emission site in the aggregating lane, delegating every classification
decision to `app.test_daemon.light_protocol`, the module both lanes already
import:

- `src/app/test_daemon/light_protocol.spl`
  - `is_load_failure(output)` — named predicate over the existing
    `unrun_reason()`, deliberately not a second copy of the token list.
  - `ran_verdict_line(path, passed, failed)` — verdict for a file that ran.
    `dropped=0`: skips are reported separately and must not be laundered into
    `dropped`, which the greenwash gate reads as non-completion.
- `src/app/test_runner_new/test_runner_main.spl`
  - `emit_spec_file_verdicts(results)`, called once before `print_summary`.
    Routes timeouts to `timeout_verdict_line`, load failures to
    `unrun_verdict_line` + `unrun_reason`, everything else to
    `ran_verdict_line`. No new formatting or reason logic lives here.

Post-fix, same command: 24 verdict lines, 14 `unrun=1`, exit still 1.

## Sabotage proof

Neutering the single call to `emit_spec_file_verdicts` drops the verdict count
from 24 to 0 while the exit code stays 1 — confirming the verdict line, not the
exit code, was the whole of the fail-open. Restoring returns 24.

## Regression spec

`test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl` pins
that an unresolvable import classifies as `unresolved-module`, that
`executed=0 dropped=1` keeps such a file red under the greenwash gate, that a
failed assertion is NOT reported as a load failure, and that the ran/unrun/
timeout lines stay mutually distinguishable.

## Open, not fixed here

`Warning: Could not load test database: Failed to load test database` appeared
**twice** on the pre-fix blink run and **zero** times on the post-fix run of the
identical command. It is therefore intermittent and not caused by the verdict
change; the most likely cause is concurrent access to the shared test database
from parallel directory runs, which
`.claude/rules/testing.md` already documents as corrupting
(`doc/07_guide/infra/testing.md` § "Runner Operational Caveats"). While it
fires, `doc/08_tracking/test/test_result.md` and `test_db.sdn` do not record the
run, compounding the same invisibility. Not root-caused — recorded so it is not
lost.
