# `bin/simple test` pays a huge fixed per-invocation cost; directory targets cannot avoid it

- **Date:** 2026-08-17
- **Status:** OPEN (root cause characterized; the fix is seed-side)
- **Severity:** HIGH — this is what capped every test sweep on this machine
- **Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple` (the **Rust seed**)

## Symptom

Sweeps do not finish. The lib sweep completed ~1/8 of its tree; `test/feature`
ended with 332 of 352 specs carrying no verdict. Runs emit a plateau of
~1900–4300 module-load warning lines and then appear to hang.

## It is NOT a hang

Three lanes killed *healthy* runs on 2026-08-17, reading silence as death:
`smtp_spec` later finished 62/62, and a crypto spec emitted its PASS at almost
exactly the moment it was killed. The plateau is a fixed setup cost being paid,
not a deadlock. No unbounded wait was found on the direct path.

## Measurements (same spec, same tree, same binary, one at a time)

| invocation | wall clock | stdout lines |
|---|---|---|
| `test <spec> --no-session-daemon --sequential` | **3.99s** | 69 |
| `test <spec>` (daemon path) | **62.4s** | 2012 |
| `test <spec>` (daemon path, immediately again) | **130.0s** | 2012 |
| `test <dir containing ONE spec> --sequential` | **>600s, killed** | 4282 |

Splitting the daemon-path log at the worker's own `child binary:` line:

```
pre-child = 59.79s      post-child = 0.27s
```

**99.6% of wall clock is spent before the spec executes**, and the spec itself
costs a quarter of a second. A companion lane measured the same shape from the
other side as `Session setup: 309585ms` ahead of an 11s spec.

The second run being *slower* than the first is the key negative result: there
is **no warm cache anywhere on this path** (`.build/*cache*` does not exist).
The full cost is paid on every single invocation.

## Where the cost goes

The daemon serves each request by spawning
`<binary> run src/app/test_runner_new/test_runner_single.spl ...`
(`src/app/test_daemon/light_daemon.spl:132`) — i.e. it runs the test runner
**from source**. Comparing the module sets named in each log:

- daemon path: **98 modules**, including the whole `10.frontend` /
  `15.blocks` compiler front end (`ast.spl`, `parser_decls.spl`,
  `flat_ast_bridge.spl`, ...)
- direct path: **4 modules**

So each invocation re-resolves and re-parses the compiler's own front end, and
the ~1943 warning lines are the diagnostics from doing so. The warnings are a
*symptom* of the re-resolution, not the cost themselves.

In the >600s directory run the last output was `[MEM] AFTER_PARSE_ARGS`; the
run never reached file discovery. That plateau is module load, before the
runner does any of its own work.

## The trap that forces sweeps onto the slow path

`--no-session-daemon` **rejects directory targets**:

```
$ bin/simple test test/01_unit/lib/nogc_sync_mut/smtp --no-session-daemon
error: expected .spl test file: test/01_unit/lib/nogc_sync_mut/smtp
```

It routes to the single-file runner, which requires a `.spl` path. So the fast
path is unavailable to exactly the directory sweeps that need it most, and any
sweep written as `test <dir>` is silently committed to the slow path.

**Workaround for sweep lanes, effective today:** enumerate the specs and run
them one file at a time with `--no-session-daemon --sequential`. That is the
3.99s path. Do not pass a directory.

## Fix status

- **Not fixable from `.spl` in this lane.** The deployed `bin/simple` is the
  Rust seed; its `test` subcommand does not execute
  `src/app/test_runner_new/*.spl` at all — instrumentation added there produced
  no output on the deployed binary. The real fix (cache the runner's resolved
  module graph, or have the daemon invoke the compiled `test` subcommand rather
  than `run <source>.spl`) is **seed-side and only provable after a bootstrap
  redeploy**.
- One tried-and-rejected change is recorded so it is not retried blindly:
  switching `light_daemon.spl:132` to the compiled
  `["test", path, "--no-session-daemon", ...]` form measured **276s and exit 1**
  — worse than the 62–130s baseline — so it was reverted rather than kept.

## Landed alongside this record

- `2b0027d5288` — session-setup phase markers emitted at **begin**, not only on
  completion, so an in-progress phase is visible instead of silence. (Seed does
  not execute this; provable after redeploy.)
- `2bc054d91e8` — `scripts/check/check-test-session-setup-budget.shs`, a
  fail-closed perf gate on the per-invocation cost that also requires a real
  `Results: N total` line. `--selftest` → `PASS — 4 fixture(s) checked`;
  scan → `PASS — 1 measurement(s) checked, ... completed in 3s (budget 90s)`.

## Unblock condition

A redeployed self-hosted `bin/simple` in which `test <spec>` on the default
(daemon) path completes within the 90s budget enforced by the gate above, with
`test <dir>` no longer forced onto the re-resolving path.

## Re-verification 2026-08-17 (fresh repro, no code change)

Confirmed by reading current source: `src/app/test_daemon/light_daemon.spl:132`
still spawns `["run", "src/app/test_runner_new/test_runner_single.spl", ...]`
(re-resolved from source every request), unchanged from the doc's citation.

Fresh independent repro (different spec than the ones tabulated above):
`bin/simple test test/03_system/check/test_daemon_env_override_passthrough_spec.spl
--no-session-daemon --sequential --timeout 180` — this spec's own body shells
out to nested daemon-path `bin/simple test` invocations, each paying the fixed
setup cost, so the outer file could not finish inside a 180s per-file budget:
`Results: 1 total, 0 passed, 1 failed` /
`SPEC FILE VERDICT: ... timeout=1 reason=child-timeout budget_ms=180000`. This
is a new, independent data point for the same defect class (a spec whose body
itself invokes `bin/simple test` is capped by the same fixed cost, compounded
per nested invocation) — consistent with, not contradicting, the doc's
existing measurements. **Verdict: confirmed OPEN, root cause and fix scope
unchanged (seed-side). No code change made in this pass — not a one-file
narrow fix per the doc's own "Fix status" section.**
