# Slim-UI startup harness (`check-ui-slim-startup.shs`)

**Package:** A01, Wave 0 of `doc/03_plan/ui/slim_kernel_plugin/plan.md`
**Requirement:** `NFR-UI-SLIM-001` (`doc/02_requirements/nfr/ui_slim_kernel_plugin.md`)
**Design:** external design § 8 (`doc/01_research/ui/slim_kernel_plugin/simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md`)
**TL;DR:** `ui_slim_startup_harness_tldr.md`

A fail-closed launch-timing harness for the H0 / T0 / T1 workloads. It exists so
that "the slim route is faster" can only ever be said on top of validated
samples: a run that produced no sample, or a sample whose transcript never
showed the workload's marker, is a FAIL or an ERROR — never a quiet pass.

## Usage

```sh
sh scripts/check/check-ui-slim-startup.shs --selftest
sh scripts/check/check-ui-slim-startup.shs \
    --binary src/compiler_rust/target/bootstrap/simple \
    --lane H0|T0|T1 [--samples N] [--warmup N] [--out DIR] [--timeout SECS]
```

Defaults: `--samples 20`, `--warmup 5`, `--timeout 300`,
`--out build/ui_slim/startup` (file `<lane>_<UTC timestamp>.sdn`).
`--selftest` runs first, is fatal, and prints `selftest: 5/5 passed`.

## Verdict convention

Last stdout line, per `.claude/rules/vcs.md`:

| verdict | exit | meaning |
|---|---|---|
| `PASS — <n> sample(s), <lane>, median <ms> ms, p95 <ms> ms, label=<diagnostic\|certified>` | 0 | every one of `n` samples was validated; `n` > 0 |
| `FAIL — <n> sample(s) attempted, <lane>, <k> invalid: <reason>` | 1 | at least one run timed out, exited non-zero, or lacked the marker |
| `ERROR — nothing was checked (<reason>)` | 2 | no binary, no clock, no PTY tool, `--samples 0`, or a concurrent build |

Two informational lines precede the verdict: the raw-SDN path, and a trailer
naming the metric, the clock, the platform RSS metric, min/max/spread.

## Lanes

| Lane | Fixture | What is launched | Marker | Metric recorded |
|---|---|---|---|---|
| H0 | `test/05_perf/ui_slim/h0_hello.spl` | `<binary> run <fixture>` | `ui-slim-h0-hello` | `launch_to_process_exit` |
| T0 | `test/05_perf/ui_slim/t0_altscreen.spl` | `<binary> run <fixture>` | `ui-slim-t0-altscreen` | `launch_to_process_exit` |
| T1 | `test/05_perf/ui_slim/t1_greeting.ui.sdn` | `<binary> ui tui <fixture>` through a **real PTY** | `ui-slim-t1-greeting` | `launch_to_marker_and_exit` |

H0 is the runtime/loader floor: one write, no imports, no UI. T0 adds only the
alternate-screen enter/restore, emitted as literal escapes so it drags no
`app.ui`/`common.ui` module into its closure — otherwise it would stop being a
provider-initialization floor and become a second T1. T1 is the real
parser-backed TUI; `SIMPLE_UI_TUI_STUB` must stay unset, or the run measures the
size-audit stub (`src/app/ui.tui/app.spl`) instead of the product path.

T1's quit is **caused by the marker, never by a sleep**: the driver waits for the
greeting on the PTY and only then sends `q`, the deterministic quit key
(`src/app/ui.tui/input.spl:29` → `UIEvent.Quit`). `expect` is preferred; a
`script(1)` + FIFO fallback does the same wait-then-type. With neither the lane
returns `ERROR — nothing was checked (no pty tool)`. `SIMPLE_UI_SLIM_PTY_TOOL=script`
forces the fallback on a host that also has `expect`.

**Fallback status, measured 2026-09-06 on macOS 15 (Darwin 25.5.0): degraded.**
Forced with `SIMPLE_UI_SLIM_PTY_TOOL=script`, the mechanics run (spawn, poll,
reap) but BSD `script(1)` refuses the FIFO stdin with
`script: tcgetattr/ioctl: Operation not supported on socket`, so the lane FAILs
for the driver's reason rather than the app's. On macOS use `expect`, which is
present at `/usr/bin/expect` in the base system. The fallback exists for a Linux
host without `expect`; it has **not** been exercised there.

Because T1's interval spans launch → greeting visible → orderly exit, it is
labelled `launch_to_marker_and_exit`, not "startup". § 8.3 forbids publishing an
unlike interval under a startup name; the harness labels rather than fabricates.
The finer milestones § 8.3 asks for (`launch_to_entry`,
`launch_to_provider_ready`, `launch_to_first_submission`, `launch_to_input_ready`)
need a child-side control channel that does not exist yet, and are therefore
absent rather than approximated.

## diagnostic vs certified

`label=certified` requires **both**: at least 100 validated samples (§ 8.5,
`NFR-UI-SLIM-001`), and no bootstrap-seed banner in any transcript. Anything
else is `label=diagnostic`, with the reason recorded in `label_reason`.

Every number obtainable today is `diagnostic`: macOS has no deployed pure-Simple
`ui` binary (plan § Blockers 1), so the only runnable binary is the Rust seed,
which prints `WARNING: this Rust-built Simple binary is a bootstrap seed only`.
A diagnostic number may be used to find a regression; it may not be used to
certify a win. Differences within noise are `INCONCLUSIVE`, never wins.

## Clocks and memory metrics — labelled, never conflated

Timestamps are taken externally around process creation, in POSIX sh only
(`perl`/`python3` are deliberately not used). The clock is probed, never
assumed, and recorded in the output as `clock:`:

| `clock` | source | note |
|---|---|---|
| `gdate_ns` | `gdate +%s%N` | coreutils on macOS (Homebrew) — used on this host |
| `date_ns` | `date +%s%N` | GNU date on Linux |
| `time_wall` | `/usr/bin/time` wall clock | last resort; BSD `date` prints a literal `N` for `%N`, which is why the probe exists |

Max-RSS is sampled in a **separate instrumented run**, never inside the timed
samples (§ 8.5: keep instrumentation out of the timing lane), and the metric name
carries its platform units:

| platform | command | metric name in SDN |
|---|---|---|
| macOS | `/usr/bin/time -l` | `max_rss_bytes` |
| Linux | `/usr/bin/time -v` | `max_rss_kbytes` |
| other | — | `max_rss_unsupported`, value `NOT_MEASURED` |

Bytes and kbytes are never compared to each other. The remaining § 8.4 rows
(PSS, sections, mappings, page faults, wakeups) are not collected here.

## Concurrent-build guard

Before the first child is launched the harness runs
`pgrep -f 'cargo|native-build|bootstrap'`. Any surviving match — including a
**peer session running the same seed**, whose path contains `bootstrap` — is an
ERROR, because § 8.5 gives the benchmark owner an exclusive runner lock and
timing under load is not evidence. Only the harness's own processes are
excluded. On a shared box, expect to wait for a quiet window.

## Raw output (SDN)

`--out` receives one file per run with: lane, metric, label and label reason,
UTC timestamp, platform, clock, PTY tool, fixture, marker, warmup/sample/invalid
counts, timeout; the binary's path, sha256 and mtime (so a stale or swapped
binary cannot be laundered into a comparison); the ms summary
(min/median/p95/max/spread); the memory row with its platform metric name; and
every raw sample in microseconds.

## Selftest fixtures (5, fatal, run first)

1. fake binary printing the marker, exit 0 → PASS
2. fake binary exiting 0 with no marker → FAIL naming the missing marker
3. fake binary hanging past the timeout → FAIL, bounded, named as a timeout
4. `--samples 0` → ERROR (a zero-sample run is never a pass)
5. missing binary → ERROR

The busy guard is bypassed only inside `--selftest`, whose fake binaries exercise
verdict logic rather than real timing.

## Measured state, 2026-09-06 (seed lane, macOS arm64)

Binary `src/compiler_rust/target/bootstrap/simple`, samples 10, warmup 3,
`clock=gdate_ns`, `pty_tool=expect`, guard-quiet runner:

```text
PASS — 10 sample(s), H0, median 61.714 ms, p95 73.074 ms, label=diagnostic
PASS — 10 sample(s), T0, median 64.599 ms, p95 71.436 ms, label=diagnostic
FAIL — 10 sample(s) attempted, T1, 10 invalid: run 1 produced no
  'ui-slim-t1-greeting' in its transcript (rc=3, last line:
  error[E1002]: function `_simple_binary` not found)
```

**These are not a baseline.** An earlier guard-quiet run of the same binary and
sample count on the same host gave H0 median 29.076 ms / T0 median 33.870 ms —
roughly half. The guard only rejects `cargo|native-build|bootstrap`; other
concurrent agent work on a shared box still moves the median by ~2x. Treat a
single diagnostic run as a smoke check, not a number to compare against.

T1's underlying cause, read from the PTY transcript, is
`error[E1002]: function '_simple_binary' not found`: `src/app/ui/cli_entry.spl`
spawns `backend_entry_tui` as a **separate process** via a `_simple_binary`
helper the seed interpreter does not resolve, so the TUI never starts and the
greeting is never painted. This is not the in-process PTY-extern defect of
`doc/08_tracking/bug/pty_externs_unusable_under_seed_interpreter_2026-09-05.md`
(resolved 2026-09-05, and about `rt_pty_*` inside a Simple program); the harness
drives the whole process from outside through `expect`. T1 stays FAIL until a
binary that can spawn its own backend is available — do not paper over it by
setting `SIMPLE_UI_TUI_STUB=1`, which would time the banner stub.

## Adding G0/G1 later

The lane table is three small functions — `lane_fixture`, `lane_marker`,
`lane_metric` — plus one `case` arm in `one_run`. To add G0 (blank native
window) and G1 (window with a visible greeting):

1. add the fixture under `test/05_perf/ui_slim/`, and its marker/metric rows;
2. give `one_run` a `G0|G1)` arm launching the GUI entry;
3. replace marker-in-transcript validation with a **presentation** check — a
   real displayed surface, not `gui_dynlib_hot_probe_tick` and not a
   checksum-only buffer (§ 8.1). A submit call or a window handle is not a
   display timestamp; where the platform cannot be observed trustworthily the
   row must read `NOT_MEASURED`, never an assumed equality with submission time;
4. add two selftest fixtures: a blank window must FAIL a G1 run, and a G0 run
   mislabelled as G1 must FAIL. Without those the gate cannot reject the exact
   fakes the plan's Wave 0 evidence gate names.
