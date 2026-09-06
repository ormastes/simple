# Perf Ladder

Performance-debugging counterpart to `.claude/skills/lib/debug_ladder.md` —
read that file first for the doc lineage and honesty conventions this file
follows (host-verified commands only; `BLOCKED: <reason>` where nothing
works; no aspirational recipes).

Verified on 2026-09-05, host darwin/arm64. Every command below was actually
run. A command not run is marked `BLOCKED: <reason>` instead of guessed.

## Measurement validity — read this FIRST

Perf work goes wrong here more often from a bad measurement than from a bad
fix. Four traps, from `.claude/rules/testing.md` "Measurement traps" plus one
caught while writing this file:

1. **Never A/B across two trees or two binaries.** An agent once measured
   "before" in the main checkout and "after" in its worktree and reported a
   **12.4x speedup**; the controlled A/B in one tree with one binary gave
   **13%**. Toggle only the change under test, hold the tree AND the binary
   fixed, and state which produced each number.
2. **Always record binary identity with any timing.** The symlink/binary a
   command resolves to gets replaced mid-session by other agents or by
   redeploys. Before trusting a number, capture:
   ```bash
   readlink -f bin/simple && stat -f "%z %Sm" "$(readlink -f bin/simple)"
   readlink -f /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple \
     && stat -f "%z %Sm" /Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple
   ```
   Verified today: `bin/simple` on this host is **not a symlink at all** — it
   is a zsh wrapper script (`file bin/simple` -> "Paul Falstad's zsh script
   text executable"), 244 bytes, dated 2026-09-04. Don't assume it is the
   binary; it dispatches to one.
3. **This box is shared and loaded.** Report an envelope (p50 and worst
   observed across N>=3 runs), never a single number — a single sample on a
   loaded host is not a measurement, it's a sample.
4. **A pipe launders the exit code — verified again today.**
   `sh scripts/check/check-startup-perf-budget.shs | tail -15; echo $?`
   printed `ERROR — nothing was checked: selftest failed (fatal)` followed by
   `rc=0` — that is `tail`'s exit status, not the guard's. Capturing first
   (`out=$(sh scripts/check/check-startup-perf-budget.shs); rc=$?`) gives the
   real answer: `rc=2`. Always capture into a variable before reading `$?`.

## Symptom -> first check

| Symptom | First check on this host |
|---|---|
| Slow startup | `scripts/check/check-startup-perf-budget.shs` (6 lanes: version/help/run_hello/run_hello_cold/smf_load/compile_hello, p50-of-7 vs `test/05_perf/startup/budgets.sdn`). Only 2 of the 6 lanes have a committed budget (`version_ms: 400`, `run_hello_ms: 450`, dated 2026-08-18); the other 4 are read by the gate but unbudgeted. **Verified today this gate ERRORs on this host: `ERROR — nothing was checked: selftest failed (fatal)`** — the gate's own selftest fails before it measures anything; treat the budget numbers above as unverified until that selftest is fixed. |
| Slow steady-state / a specific hot function | `simple perf record <test-path> <cohort-id> <duration-ms>` then `simple perf explain <test-path>` (workflow below) for a tracked test; for an ad-hoc function, use the debug ladder's probe-script tier (step 3C there) timed with `rt_time_monotonic_ns()` around the call, same binary/tree discipline as above. |
| Memory growth / RSS | `scripts/check/check-memory-budget.shs`. **Verified today this also ERRORs on this host**: `selftest: successful command yielded no measurement` / `ERROR — nothing was checked (selftest failed)`. Also `bin/simple mem <top|diff>` for ad-hoc snapshot diffing — **verified BLOCKED on this host**: `bin/simple mem` returns `error: unknown command 'mem'` because `bin/simple` is bootstrap-only here (no `mem`/`run`/`test`); `mem` is wired only in the full self-hosted CLI's `command_registry.spl`/dispatch table, not deployed on this host. |
| Quadratic blowup on input size | Sweep the input size (not one point) with a probe script per the debug ladder's step 3C, same binary/tree, and look for a specific pattern: **reassigned `array = array.push(value)` is proven quadratic here** (COW-copies the whole array per write); **bare `array.push(value)`** is not yet proven quadratic — see the worked example below. `scripts/check/check-cross-language-perf.shs` exists for cross-language compute comparisons (not run today — see BLOCKED list). |
| Regression vs a recorded baseline | `simple perf compare <test-path> <cohort-id> <candidate-ms>` against the test's `ApprovedBaseline` (workflow below); or the pinned-mechanism gate `scripts/check/check-perf-regression-tests.shs` if the regression is one of the ~191 already-named fixes. |

## The real `simple perf` workflow

`simple perf` **is wired** (`src/app/cli/dispatch/table.spl:550-555` ->
`src/app/perf/main.spl`) but was absent from `src/app/cli/command_registry.spl`
(the table that drives help/discovery) until this file's companion fix
(2026-09-05) added it there. Real usage, verified today:

```bash
SEED=/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple
"$SEED" run src/app/perf/main.spl
# Usage: simple perf <record|compare|explain|baseline promote> ...
#   record <test-path> <cohort-id> <duration-ms>
#   compare <test-path> <cohort-id> <candidate-ms> [--confirmed]
#   explain <test-path>
#   baseline promote <test-path> <cohort-id>
```

Worked example (run today, real command against a real test path):

```bash
"$SEED" run src/app/perf/main.spl record test/05_perf/dummy_probe.spl cohortA 123
"$SEED" run src/app/perf/main.spl explain test/05_perf/dummy_probe.spl
```

**Both failed identically on this host** with:
```
perf-error: could not open or parse doc/08_tracking/test/test_db.sdn
(existing file is unreadable or migration from
doc/08_tracking/test/test_db_stable.sdn failed)
```
Root cause, verified directly: `doc/08_tracking/test/test_db.sdn` carries a
`#sdn-crc32:1415345513` header that does **not** match its own body's CRC32
(computed independently: `3879582927`) — the tracked file is stale/corrupt
relative to its own checksum, not a `simple perf` bug. Regenerating it via a
full test run should fix this; `bin/simple test` is itself bootstrap-only on
this host (prints HELP, does not build/run), so regenerating it is
**BLOCKED here** pending a full-CLI binary. Treat `record`/`compare`/`explain`
as blocked by this data-file defect, not by the CLI, until `test_db.sdn` is
regenerated.

`baseline promote` was not exercised (would hit the same `test_db.sdn`
failure as `record`/`explain` — not re-run separately).

## Which gates to run and what each measures

| Gate | Measures | Tier |
|---|---|---|
| `scripts/check/check-perf-regression-tests.shs` | ~191 named perf-fix mechanisms, pinned by exact `file:needle` source-text match — **not** measured wall time | push, ADVISORY |
| `scripts/check/check-startup-perf-budget.shs` | 6 startup-wall-time lanes vs `test/05_perf/startup/budgets.sdn` (2 of 6 budgeted) | on-demand |
| `scripts/check/check-memory-budget.shs` | RSS/memory budgets | on-demand |
| `scripts/check/check-lint-cost-budget.shs` | lint wall-time budget (see `.claude/rules/commands.md` "Fast Path" for the underlying cost table) | on-demand |
| `scripts/check/check-cross-language-perf.shs` | cross-language compute-compile comparisons | on-demand |

Verified today: `check-perf-regression-tests.shs` runs to completion and
reports `FAIL — 191 mechanism(s) checked, 4 regressed` (see
`doc/08_tracking/bug/perf_regression_tests_4_mechanisms_red_2026-09-05.md`
for the 4 named mechanisms, what each pins, and the unblock condition for
each — filed, not fixed, per instruction). `check-startup-perf-budget.shs`
and `check-memory-budget.shs` both **ERROR on selftest** on this host before
measuring anything (exact messages above) — do not trust their budget
numbers until that is fixed. `check-lint-cost-budget.shs` and
`check-cross-language-perf.shs` were not run for this file (out of scope of
today's survey); do not assume they pass.

## Worked examples from the existing bug corpus (symptom classes)

- `doc/08_tracking/bug/stage3_quadratic_transient_heap_promote_2026-09-02.md`
  — a stage-3 transient-heap-promotion quadratic-growth case.
- `doc/08_tracking/bug/web_tile_paint_ops_quadratic_growth_2026-09-05.md` —
  a worked example of the "quadratic blowup on input size" row above: the
  paint-op list was built with repeated bare `Array.push` across multiple
  node passes; the record is explicit that the admitted runtime has evidence
  *reassigned* `array = array.push(value)` can be quadratic but does **not**
  yet prove the same for bare `array.push(value)` — the hardening
  (preallocate `3 * node_count`, write by index, one linear finish) was
  applied regardless, with classification as a genuine performance fix left
  pending real before/after profiling. This is the right level of honesty:
  don't claim a measured regression you haven't measured.

## Explicitly BLOCKED on this host (verified 2026-09-05)

- `command -v perf` -> not found (exit 1). `command -v flamegraph` -> not
  found (exit 1). `src/app/profiling/profile.spl` needs both on PATH; neither
  is available on this macOS host, so that profiler is BLOCKED here, not
  broken.
- `bin/simple mem <top|diff>` -> `error: unknown command 'mem'` — `mem` is
  registered in `command_registry.spl`/dispatch table for the full
  self-hosted CLI, which is not deployed as `bin/simple` on this host
  (bootstrap-only; see `.claude/skills/lib/debug_ladder.md` environment
  facts, which apply identically here).
- `simple perf record|compare|explain` against a real test path -> blocked by
  the corrupt `test_db.sdn` CRC mismatch described above, not by the CLI.
- `scripts/check/check-startup-perf-budget.shs` and
  `scripts/check/check-memory-budget.shs` -> both ERROR on their own
  selftest before measuring anything (exact messages above); do not rely on
  either gate's verdict until its selftest is repaired.

## Hard rules (inherited from the debug ladder, apply identically to perf)

- Never claim PASS from absent output — `executed=0`/`0 lane(s) measured` is
  not a pass.
- Never symbolize or compare against a binary that isn't the one you timed.
- Never treat "number changed" as evidence without stating tree, binary,
  sample count, and host load at the time.
- Never widen a pinned mechanism's needle to make a red gate pass — repin it
  to the real new location of the same guarantee, and say so, per the
  worked example in `perf_regression_tests_4_mechanisms_red_2026-09-05.md`.
