# rt_fork_parent_wait_bounded() exited its read loop early and truncated captured output SILENTLY

- **Status:** FIXED 2026-08-18
- **File:** `src/runtime/runtime_fork.c`
- **Guard:** `sh scripts/check/check-fork-capture-complete.shs`
- **Cited by:** `doc/02_requirements/infra/supervised_test_runner.md` (defect 4)

## Exact early-exit condition

Not "read() == 0 treated as EOF", not a missing fd, not a fixed buffer: the loop
ended at the **inherited-fd grace cap**. After the directly-forked child is
reaped, a descendant can still hold the pipe write end. The loop counted 40
consecutive no-data poll cycles (`FORK_EXIT_GRACE_POLLS`, ~2 s) and then broke
with `cleanup_descendants = 1`, SIGKILLed the process group, and drained for
100 ms. Everything the descendant had not yet written was destroyed **by the
kill itself**, so `capture->total` never counted it and `capture_finish()`
emitted no marker. The reader saw a short, clean, plausible capture.

Two smaller defects on the same path:
- the main read loop treated `EINTR` as end-of-stream (`*open_ptr = 0`),
  silently ending a capture on any signal arriving before a byte transferred --
  `drain_capture_fds()` retried correctly, the main loop did not;
- a genuine read error / `POLLERR` closed the stream with no report.

## Reproduction (true vs captured)

`scripts/check/fixtures/fork_capture_probe.c`, mode `early`: child exits
immediately, a grandchild holds the pipe fd and writes after 5 s of silence.

| runtime | bytes written | bytes captured | marker |
|---|---|---|---|
| before fix | 503,808 | **0** | none |
| after fix  | 503,808 | 95 (marker only) | `[capture incomplete: ...]` |

Control cases, after the fix: 1,048,576 bytes/stream -> captured 1,048,576
exactly, no marker; 5 MiB -> bounded to the 4 MiB retention limit with
`[output truncated: N bytes omitted]`.

## Fix

Capture is now either byte-exact or **bounded and announced**. Any stream that
did not reach real EOF gets an explicit
`[capture incomplete: <reason>; stream never reached EOF]` line naming the
reason (timeout / poll failure / grace-period descendant kill / read error).
`EINTR` in the main read loop now retries instead of ending the stream.
Post-kill EOF is deliberately NOT treated as natural EOF -- it exists only
because we killed the writer.

## Runtime scope

C runtime only. `grep -rn rt_fork src/compiler_rust/runtime/src/` returns
nothing; the only Rust hit is `native_project/tests.rs:2203`, a test asserting
the C symbol names are linked. No parallel Rust implementation, so the stale
Rust-archive hazard
(`stage3_links_stale_rust_runtime_archive_runtime_fixes_are_noops_2026-08-17.md`)
does not apply to this symbol. Verified against a privately built probe binary
linking the edited `runtime_fork.c` directly -- no `bin/simple` rebuild.

## Guard

`check-fork-capture-complete.shs` -- `PASS — <n> capture case(s) checked` / FAIL
1 / `ERROR — nothing was checked` 2 (no compiler is ERROR, never a pass).
`--selftest` is fatal and runs a marker-ablation negative control. Full
negative control recorded: with `runtime_fork.c` reverted to the pre-fix commit
the guard printed
`FAIL — 3 capture case(s) checked; early: wrote 524288 bytes, captured 0, and the capture does NOT announce it is incomplete`.
