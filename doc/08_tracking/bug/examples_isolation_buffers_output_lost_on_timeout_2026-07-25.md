# `examples/**` isolation wrapper buffers child output and discards it when the run is killed — any slow example looks like a silent exit-0

- **ID:** examples_isolation_buffers_output_lost_on_timeout_2026-07-25
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** high (masks evidence; makes failures indistinguishable from success)
- **Found via:** `widget × host-WM` showcase-matrix cell producing 2 lines of
  output and exit 0.

## Symptom

```
$ SIMPLE_WM_HEADLESS_CAPTURE=1 <simple> run examples/06_io/ui/wm_widget_showcase_gui.spl
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
Build and use the pure-Simple bin/simple instead.
$ echo $?
0
```

Two lines, both from the parent. No status key, no PPM, no error — and **exit 0**.
The cell was recorded as BLOCKED on the assumption the wrapper was window-only.
It was not: the code ran fine and its output was thrown away.

## Root cause

`bin/simple run <path under examples/>` re-execs itself as an isolated child
(`src/compiler_rust/driver/src/cli/basic.rs:108-115` →
`src/compiler_rust/driver/src/cli/examples_safety.rs`).

`run_child_with_timeout` (`examples_safety.rs:124-187`):

- stdout/stderr are piped and drained on threads into **in-memory `Vec<u8>`**
  (`spawn_pipe_drain`, line 116-122),
- the buffers are printed only **after** the wait loop completes
  (lines 174-179).

So when the watchdog kills the child on timeout (lines 148-151), every byte the
child already printed — including the literal first `print` of `main()` — is
still sitting in the buffer and is discarded.

The draining itself is correct and deliberate: the comment at lines 133-138
explains it exists to avoid a full-pipe deadlock. **The bug is not the draining,
it is `buffer-then-dump-at-exit` instead of `tee-as-you-go`.**

`rt_print_str` flushes per call
(`src/compiler_rust/runtime/src/value/sffi/io_print.rs:81-98`), so the child's
own flushing is not at fault.

## Why this matters beyond one cell

Any `examples/**` script whose runtime can exceed the timeout shows **zero
output and exit 0**, regardless of correctness. An exit-0 with no evidence reads
as success to any check that inspects only the return code. Three showcase-matrix
host-WM cells were misattributed to a "window-only wrapper" gap because of this.

Contributing factor: `run_headless_capture`'s worst-case wait budget is
bridge 300000ms + frame 180000ms ≈ **8 minutes**, comfortably above common
harness timeouts — so the loss window is hit routinely, not rarely.

## Verification

Setting `SIMPLE_EXAMPLE_ISOLATED_CHILD=1` makes the process treat itself as the
already-isolated child (`examples_safety.rs:42`), skipping the re-exec. Same
command then streams normally: **169,612 lines** vs 2.

## Fix direction

In `run_child_with_timeout`, replace `spawn_pipe_drain` with a tee: read chunks
and write them straight to the parent's stdout/stderr (flushing per chunk) while
still draining concurrently, so the deadlock protection at lines 133-138 is
preserved. Output then survives a kill.

Optionally also lower the bridge/frame defaults for CI, but that is a mitigation
— streaming is the fix. Note this code is in the Rust seed
(`.claude/rules/bootstrap.md` keeps the seed bootstrap-only), so landing it
requires a seed rebuild, which invalidates cached objects for concurrent
sessions — coordinate before doing it.

## Second cause found 2026-07-25: a 10s in-process watchdog, and it misreports its own limit

Bypassing the isolation re-exec with `SIMPLE_EXAMPLE_ISOLATED_CHILD=1` makes
output stream (169,612 lines vs 2) but the run still dies:

```
[watchdog] wall-clock timeout (10s) exceeded
[watchdog] crash report: .simple/logs/crash_<pid>.log
error: timeout: execution exceeded 0 second limit
```

So there are **two** independent kills on this path, and fixing only the
buffering does not make the cell runnable:

1. the isolation wrapper's buffer-then-dump (above), and
2. a **10-second default in-process watchdog**, against a
   `run_headless_capture` whose bridge+frame waits budget ~8 minutes
   (300000ms + 180000ms). It cannot finish, ever, at the default.

**Correct invocation** for this lane: set `SIMPLE_TIMEOUT_SECONDS` (e.g. 900),
which both raises the watchdog and disables the isolation re-exec
(`examples_safety.rs:38,42` — `examples_timeout_disabled()` keys off exactly this
variable).

**Bug within the bug — the limit is misreported.** The watchdog says `(10s)` but
the surfaced error says `exceeded 0 second limit`
(`src/compiler/00.common/error.spl:257`, `src/compiler_rust/compiler/src/error.rs:514`,
both interpolating a `secs`/`timeout_secs` that arrives as **0**). Reading "0
second limit" suggests a zero/misconfigured limit rather than the real 10s
default, which sends a reader looking in the wrong place. The watchdog's own
value and the value passed into the error type are not the same variable — they
should be, or the error should not claim a number it does not have.

## Secondary observation (separate issue, not filed here)

The streamed log is dominated by repeated `info: Common mistake detected`
diagnostics (e.g. `self.x = value` hints from
`src/lib/gc_async_mut/gpu/engine2d/backend_qualcomm.spl:112`) — ~167k lines in
25s. This matches the `2D × headless` cell's recorded "75k lines dominated by
diagnostic spam" and is worth its own investigation: an advisory hint should not
be emitted per-evaluation.
