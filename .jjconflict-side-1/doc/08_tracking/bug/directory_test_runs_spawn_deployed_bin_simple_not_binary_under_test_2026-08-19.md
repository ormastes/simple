# Directory test runs spawn the deployed `bin/simple`, not the binary under test — 2026-08-19

**Status:** FIXED (`find_simple_binary()` now resolves the running executable
through the `/proc` self-exe link).

**Severity:** measurement integrity. Nothing is miscompiled; instead any lane
that evaluates an unshipped build with a DIRECTORY target silently measures the
deployed build and attributes its failures to the new one.

## What this closes: the premise of the 2026-08-18 taxonomy is wrong

`doc/08_tracking/test/failure_taxonomy_system_unit_2026-08-18.md` reported
`OBJECT_TYPE_ERASURE` as still the largest failure class — 369 of 450 failed
examples in the unit shards — **on the class-resolution-fix binary**
`/mnt/data/tmp/classfix/release/simple` (mtime 2026-08-18 14:27, matching
`2d461e78c9c`), and concluded a second independent defect must survive that fix.
Representative errors quoted there:

```
semantic: method `executed_files` not found on type `object` (receiver value: CoverageCollector(line_hits: {}, function_calls: {}))
semantic: undefined field 'width': cannot access field on value of type 'object'
```

There is no second path. Every shard in that record was a directory target, and
a directory run spawns one child process per spec. A `ps` snapshot taken during
`/mnt/data/tmp/classfix/release/simple test test/01_unit/app/ui` shows the
children verbatim:

```
timeout --kill-after=5s 120s bin/simple run test/01_unit/app/ui/color_spec.spl
timeout --kill-after=5s 120s bin/simple run test/01_unit/app/ui/windows_compat_spec.spl
```

`bin/simple` resolves to
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(59645008 bytes, mtime 2026-08-18 10:12) — a **pre-fix** build, not the
59613656-byte class-fix binary the record names.

Same spec run as a SINGLE-FILE target (evaluated in-process, no child spawn):

| binary | `test/01_unit/app/ui/ratatui_backend_spec.spl` |
|---|---|
| deployed `bin/simple` (pre-fix) | `Results: 24 total, 1 passed, 23 failed` — ``semantic: method `is_valid` not found on type `object` (receiver value: MockTerminal(is_active: true, width: 80, height: 24))`` |
| `/mnt/data/tmp/classfix/release/simple` (`2d461e78c9c`) | `Results: 24 total, 24 passed, 0 failed` |

`test/01_unit/app/ui/window_model_spec.spl` likewise goes 4 failed -> 4 passed,
and `test/03_system/coverage/coverage_core_spec.spl` (the source of the
`CoverageCollector` quote) is `Results: 26 total, 26 passed, 0 failed` on the
fixed binary. Corroborating the source reading: `ClassInstance::new` has **zero**
callers after `2d461e78c9c`, so no live code can still produce the value shape
those errors describe.

## Mechanism

`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:101`
`find_simple_binary()` resolved, in order: `cli_get_args()[0]` when it "looks
like the compiled binary", then `SIMPLE_RUNTIME`, then a literal candidate list
beginning `bin/simple`.

**`cli_get_args()` does not return the executable.** Measured directly on both
binaries with a probe script:

```
$ simple run argv_probe.spl extra1
len=2
arg[0]=argv_probe.spl
arg[1]=extra1
```

argv[0] is the SCRIPT. The `test` path has the same shape, so
`self_exe.ends_with("/simple")` was never true and the branch never fired.
Resolution fell straight through to `bin/simple` — the deployed symlink — which
is why the same spec passes as a single-file target and fails inside a directory
run on the very same binary.

The result is memoized in the module-global `_cached_binary_path`, so the first
wrong answer is reused for every spawn in the run.

## Fix

Resolve the running executable from the kernel instead of from argv. Added a
`/proc/self/exe` (Linux) / `/proc/curproc/file` (FreeBSD) probe to
`find_simple_binary()`, placed after the explicit `SIMPLE_RUNTIME` override and
before the `bin/simple` candidate list. The link is CANONICALISED in the parent via `rt_path_absolute`
(std::fs::canonicalize) — it must never be handed to the spawner verbatim, see
the exit-125 note below. Hosts without `/proc` (macOS, Windows)
fall through to the previous behaviour — that gap is stated, not closed.

The dead argv[0] branch above it is left in place and is now documented with the
measurement showing why it cannot fire; it is harmless and still correct for any
future caller that does pass a real executable path.

Verification, all on `/mnt/data/tmp/classfix/release/simple`, `test/01_unit/app/ui`:

* pre-fix children: `timeout --kill-after=5s 120s bin/simple run .../color_spec.spl`
* post-fix children: `timeout --kill-after=5s 120s /mnt/data/tmp/classfix/release/simple run .../web_render_backend_api_spec.spl`

### RED / GREEN

All three rows are `/mnt/data/tmp/classfix/release/simple test test/01_unit/app/ui
--no-cover-check`, same binary, same target, same tree — only the resolver changed.

| | verdict |
|---|---|
| RED (pre-fix) | `Results: 1762 total, 1147 passed, 615 failed, 607 skipped` |
| GREEN (post-fix) | `Results: 1811 total, 1589 passed, 222 failed, 220 skipped, 3 timed out (unverified)` |
| independent control (`SIMPLE_RUNTIME` pointed at the same binary, pre-fix source) | `Results: 1811 total, 1594 passed, 217 failed, 215 skipped, 3 timed out (unverified)` |

The control matters: it reaches the same place by a different route (the
`SIMPLE_RUNTIME` branch, which did fire), so the improvement is attributable to
*which binary the children ran*, not to the resolver edit itself.

Two named specs, RED -> GREEN:

* `test/01_unit/app/ui/ratatui_backend_spec.spl`: `FAIL (1 passed, 23 failed)` -> `PASS (24 passed)`
* `test/01_unit/app/ui/window_model_spec.spl`: `FAIL (0 passed, 4 failed)` -> `PASS (4 passed)`

Positive control that had to stay green:
`test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl` —
`Results: 6 total, 6 passed, 0 failed`.

An intermediate attempt that passed the raw `/proc/self/exe` link to the spawner
made every child exit 125 (`Results: 132 total, 0 passed, 132 failed`) because
`timeout` re-resolves the link against itself. That is why the path is
canonicalised in the parent; the failure is recorded here so the shortcut is not
retried.

## Specs

* Reproducing + defect class:
  `test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl` —
  asserts `cli_get_args()[0]` is not the executable (the defect's premise),
  that `find_simple_binary()` returns a path that actually exists, that it
  resolves to the self-exe link rather than the deployed one, and that the
  memoized answer is stable. Carries two positive controls so the assertions
  cannot pass vacuously.

## Consequence for the taxonomy record

`doc/08_tracking/test/failure_taxonomy_system_unit_2026-08-18.md` section 0 and
both ranked `OBJECT_TYPE_ERASURE` rows are artifacts of this defect. That record
has been annotated with a retraction header and left otherwise unaltered; the
counts must be re-measured with a binary the children actually run.

## Not fixed here

* macOS / Windows have no `/proc`; resolution there still falls through to the
  candidate list. A portable "current executable" extern (`std::env::current_exe`
  behind an `rt_*` symbol) is the durable answer and does not exist yet —
  `current_executable_path` is imported by
  `src/lib/nogc_sync_mut/platform_measurement_observer.spl:13` but is defined
  nowhere in the tree, so that import is already dangling.
* The same argv[0] assumption appears in
  `src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:70`,
  `src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl:228`,
  `src/app/test_runner_new/test_runner_single.spl:188` and
  `src/app/test_runner_new/test_runner_client.spl:190`. They were left alone to
  keep this diff minimal; they carry the same defect and should move to the same
  resolver once a portable extern exists.
