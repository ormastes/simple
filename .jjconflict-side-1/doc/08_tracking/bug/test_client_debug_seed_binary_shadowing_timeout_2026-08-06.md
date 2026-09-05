# `bin/simple test` daemon lanes preferred a stray Rust debug-seed build over `bin/simple`, making slow specs blow through every `--timeout` override — source-fixed in 3 files

- **Date:** 2026-08-06
- **Severity:** high — silently degrades `bin/simple test <spec>` (the default,
  no-flags invocation) for **every** user of a shared dev box that ever ran
  `cargo build` (debug profile) in `src/compiler_rust/`, for the **entire
  lifetime** of the light-test-daemon process. Not limited to the two specs
  that surfaced it.
- **Status:** FIXED. Source-fixed in three duplicated copies of the same
  `simple_binary()` helper; confirmed live at runtime (modules load from
  `.spl` source, no rebuild needed) via `ps` inspection of the spawn chain
  (release binary throughout, no `target/debug/simple` anywhere), and
  confirmed by a clean default-lane
  `bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl --timeout 400`
  run: `10 total, 10 passed, 0 failed`, exit 0, ~133s wall (see "Evidence").
  The `--timeout 400` was needed only to absorb this box's concurrent-session
  CPU contention (load average 17+ during this investigation) — at the stock
  120s default the same spec still timed out on this loaded box even with
  the fix applied and the spawn chain confirmed all-release. Plain
  `bin/simple test <spec>` (no flags) on a quiet box is expected to pass in
  ~1-2 minutes; this was not independently confirmed because a quiet box
  was not available during this investigation.

## Symptom (as reported)

Two specs — `test/01_unit/os/compositor/compositor_occlusion_spec.spl` and
`test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl` — reliably hit
`Process timed out` at ~120-140s wall time when run via `bin/simple test`,
**regardless** of `--timeout` flag value, `SIMPLE_TIMEOUT_SECONDS`, or an
external shell `timeout` wrapper set to 600s/1200s. Both specs were confirmed
to pass cleanly when run standalone outside the daemon lane (e.g.
`--no-session-daemon`), and the glyph-run spec passed 4/4 in 185s via
`bin/simple test` alone (no other suite specs competing) in an earlier
session — inconsistent with a fixed per-process wall clock.

## Root cause

`src/app/test_runner_new/test_runner_client.spl` (the light-daemon client),
`src/app/test_daemon/light_daemon.spl` (the light-daemon server), and
`src/app/test_daemon/main.spl` (`simple test-daemon start/stop/run`) each
carry their own copy of a `simple_binary()` helper that resolves which
`simple` executable to spawn for test execution. All three copies had the
same defect: after failing to trust `argv[0]` (a documented, legitimate
guard — argv[0] is often the interpreter's own source-mode path, not an
executable), the fallback chain checked
`src/compiler_rust/target/debug/simple` **before** `bin/simple`:

```
if raw.len() > 0 and (raw[0].ends_with("/simple") ...) and rt_file_exists(raw[0]):
    return raw[0]
if rt_file_exists("src/compiler_rust/target/debug/simple"):   # <- wrong order
    return "src/compiler_rust/target/debug/simple"
if rt_file_exists("bin/simple"):
    return "bin/simple"
```

`src/compiler_rust/target/debug/simple` is a routine `cargo build` byproduct
— it exists on this box because *someone* ran a debug build at some point,
not because anyone opted into using it for testing. Per
`.claude/rules/bootstrap.md`, the Rust seed (debug or release) is
bootstrap-only and must never be the day-to-day `bin/simple`. A debug-profile
interpreter is roughly 10-50x slower than the deployed release
`bin/simple` for compute-heavy specs (SIMD/render paths especially).

Critically: **`light_daemon.spl`'s copy is the one that actually mattered**.
`ensure_daemon()` (in `test_runner_client.spl`) resolves `simple_binary()`
once, to *launch* the daemon process — with the fix already applied to that
file, the daemon process itself now starts correctly as `bin/simple`. But
the daemon is long-lived (serves every `bin/simple test <spec>` request,
across sessions and users, until stopped), and it calls its **own**,
separately-defined `simple_binary()` once at `main()` startup
(`light_daemon.spl:100`, now :113) to decide what binary to spawn for each
test it serves for its *entire remaining lifetime*. Inside the daemon's own
process, `argv[0]` (via `cli_get_args()`) is the daemon's own script path
(`src/app/test_daemon/light_daemon.spl`), which does not end in `/simple` —
so the `argv[0]` guard reliably fails inside the daemon, and execution always
fell through to the buggy debug-first fallback. **Why `argv[0]` fails inside
the daemon specifically (vs. resolving to the invoking `bin/simple`) is not
established** — only that the daemon reliably falls through the guard,
confirmed by every daemon process observed during this investigation
(`ps` showed `src/compiler_rust/target/debug/simple run
src/app/test_daemon/light_daemon.spl` even for daemons freshly spawned by a
correctly-invoking `bin/simple test`, immediately after the
`test_runner_client.spl` fix alone, before the `light_daemon.spl` fix
landed).

Because the daemon pins to whatever binary its own startup resolved to and
never re-resolves, once a debug-pinned daemon exists it stays that way until
someone kills it — explaining why the symptom looked immune to `--timeout`:
**the override *is* honored** (the daemon's own bounded wait,
`process_run_bounded(binary, ..., timeout_ms, ...)` in
`light_daemon.spl:handle_request`, correctly uses the caller's requested
timeout), it just can't rescue a run that, under a debug interpreter, was
never going to finish inside any humanly-patient timeout.

## Evidence

| time (2026-08-06) | source state | debug binary present? | daemon's spawn chain (`ps`) | result |
|---|---|---|---|---|
| 15:48 | pre-fix | yes | `src/compiler_rust/target/debug/simple` | `Process timed out`, ~138s |
| 16:01 (fresh daemon after `kill -9`) | pre-fix | yes | `src/compiler_rust/target/debug/simple` (still) | `Process timed out`, ~139s |
| 16:04 | pre-fix, debug binary **moved aside** | no | falls through to `bin/simple` (only candidate left) | **EXIT:0, 108s, 10/10 passed** |
| 16:12 (fresh daemon after both `.spl` fixes) | fixed | yes (restored) | `bin/simple run light_daemon.spl` → `bin/simple run test_runner_single.spl` → `bin/release/.../simple run <spec>` — release throughout | ran (timing result confounded by concurrent load, see below) |

The 16:04 row is the cleanest single A/B: identical (still-buggy) source,
only the debug binary's presence changed, and that alone flipped the result
from a guaranteed timeout to a clean pass in under 2 minutes.

The 16:12+ row confirms the **fix is live** — `.spl` modules load from
source at runtime, not from a frozen compiled binary, so editing
`test_runner_client.spl` and `light_daemon.spl` took effect on the very next
daemon spawn, no bootstrap/redeploy needed. Repeated `ps` snapshots after the
fix, across three separate `bin/simple test` invocations, never showed
`target/debug/simple` anywhere in the spawn chain again.

This investigation session ran on a shared dev box under genuine concurrent
load from unrelated sessions (`uptime` showed load average 17.5 with 10
concurrent `bin/simple test`/`bin/simple run` processes at one point,
including specs this session never invoked, e.g. `riscv_fpga_linux_spec.spl`,
`async_basics_spec.spl`). Two post-fix runs of the compositor spec at the
**default 120s** daemon-lane timeout still hit `Process timed out` at
~139-140s despite the spawn chain being confirmed all-release — that is CPU
contention inflating a normally ~85-110s render-heavy spec past 120s, not the
debug-seed defect (independently and directly disproven by the 16:04 row).
A follow-up run with `--timeout 400` (generous room to absorb the same
contention, still through the default daemon lane, no `--no-session-daemon`)
closed this out cleanly:

```
$ bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl --timeout 400
...
Results: 10 total, 10 passed, 0 failed
Duration: 132894ms
PASS test/01_unit/os/compositor/compositor_occlusion_spec.spl
```

exit 0, ~153s wall (133s of that inside the spec itself), all under a
release-only spawn chain. The residual sensitivity to the 120s *default* on
a heavily-loaded shared box is a separate, pre-existing concern (the default
daemon-lane timeout has no headroom for concurrent-session contention) —
out of scope for this bug, noted under Recommendation.

## Fix

Reordered the fallback chain in all three copies so `bin/simple` (and
`/proc/self/exe` where present) is tried before any `target/debug/simple`
candidate, matching the already-correct ordering used elsewhere (e.g.
`test_executor_parsing.spl:find_simple_binary()`,
`test_runner_single.spl:find_simple_binary()`, and the Rust seed's own
`find_simple_binary()` in `execution.rs`, which uses
`std::env::current_exe()` and never puts a debug candidate before a
release one).

Files changed:
- `src/app/test_runner_new/test_runner_client.spl` (`simple_binary()`)
- `src/app/test_daemon/light_daemon.spl` (`simple_binary()`) — the one that
  actually determined the observed symptom
- `src/app/test_daemon/main.spl` (`simple_binary()`, `simple test-daemon
  start/stop/run` CLI)

## Investigated and eliminated

- `src/compiler_rust/driver/src/cli/test_runner/execution.rs:per_test_timeout_secs()`
  reads `SIMPLE_TEST_TIMEOUT` (default 60s, 120s under a `test/.../system/`
  path component, 240s for `@qemu`-tagged specs) and drives an in-process
  watchdog (`start_watchdog`). This looked promising (matches the reported
  magnitude) but is a dead end: no `.spl` file anywhere sets
  `SIMPLE_TEST_TIMEOUT` (confirmed both directions — grepped every setter and
  every reader), and the function is only reachable from the Rust CLI's own
  native `test` subcommand execution path, which is never what gets spawned
  — every `.spl`-side child invocation spawns `["run", <file>]`, not
  `["test", <file>]` (`build_child_args()` in `test_executor_parsing.spl`,
  and `light_daemon.spl`'s own child-arg construction). This function cannot
  fire on the reported path. `SIMPLE_TIMEOUT_SECONDS` is the variable the
  `.spl` layers actually use, and it is correctly plumbed down to
  `process_run_bounded`'s `timeout_ms` argument at every layer checked
  (`test_runner_execute.spl`, `test_runner_single.spl`).
- `run_with_timeout` in `src/lib/nogc_sync_mut/src/infra.spl:686` (the
  `.spl`-level "Process timed out after {N}ms" `IoError` message) is never
  called anywhere in the test-runner path — the literal string observed at
  the terminal comes from the lower-level Rust extern implementing
  `process_run_bounded`/`process_run_timeout`
  (`src/compiler_rust/compiler/src/interpreter_extern/system.rs:165,228`),
  which is the correct, working bounded-wait primitive that every `.spl`
  layer calls into. This is not itself a bug — it is the mechanism that
  faithfully reports "your child was killed because it exceeded the timeout
  you (or a default) gave it," which is exactly what happens once a debug
  seed makes that deadline unreachable.
- The light-request protocol's 600s cap (`LIGHT_REQUEST_MAX_TIMEOUT_MS` in
  `light_protocol.spl`) and the `long_timeout_bypass` logic in
  `test_runner_client.spl` are correctly implemented and not implicated —
  they only matter for `--timeout` values above 600s, and the reported
  symptom fires well under that.

A second spec confirms the fix generalizes (not specific to the compositor
spec's render profile):

```
$ bin/simple test test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl --timeout 400
...
Results: 4 total, 4 passed, 0 failed
PASS test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl
```

exit 0, 34s wall — through the default daemon lane, no `--no-session-daemon`.

## Recommendation

- Re-run `bin/simple test test/01_unit/os/compositor/compositor_occlusion_spec.spl`
  and `bin/simple test test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl`
  (no flags — the default daemon lane) on a quiet box to get an
  uncontended timing confirmation; both are expected to pass in ~1-2 minutes.
- Consider a light daemon self-check (e.g. print the resolved binary path to
  its log at startup) so a future debug-seed mis-pin is visible immediately
  instead of manifesting as an unexplained timeout.
- Consider `pkill -f light_daemon.spl` (or `simple test-daemon stop`)
  as the first troubleshooting step whenever a spec that passes standalone
  fails only through the default `bin/simple test` daemon lane — the daemon
  can carry stale/wrong binary state across an unrelated source fix until
  explicitly restarted.
