# Process-tree RSS watchdog is a Perl hard dependency

Date: 2026-09-24. Status: open. Owner decision needed on sequencing.

## Problem

`scripts/resource/process-tree-rss-watchdog.pl` is the only RSS guard for all
bootstrap workloads. It is reached through
`scripts/bootstrap/run-process-group-timeout.shs`, `bootstrap-from-scratch.sh:2083`,
and `scripts/check/lib/bootstrap-stage3/command-snapshot.shs:374`. It is an
~850-line Perl program. That breaks the repo rule that code is `.spl`/`.shs`
and that only the 3 bootstrap scripts may be other shells. No pure-Simple or
`.shs` twin exists: a grep of `src/` and `scripts/` for
`rss_watchdog|process_tree_rss|rss_guard` in `*.spl` finds nothing.

Perl is available where the guard runs today. `scripts/setup/bootstrap-prereqs.shs`
lists `perl` for every host (the Windows row is line 275), and Git for Windows
ships MSYS perl. So the risk is policy and maintenance, not availability. The
guard depends on MSYS/Cygwin-specific Perl: `Cygwin::posix_to_win_path` and
`/proc/<pid>/winpid`. Native MSWin32 perl is refused.

## Why it is not a one-line port

- The guard must run **before** any Simple compiler is trusted, because it
  guards the stage-1/2 builds themselves. A pure-Simple guard needs a runnable
  Simple binary, which is exactly what bootstrap is still producing.
- POSIX semantics it relies on: `fork`, `setsid`/`setpgid`, a race-free exec
  gate (pipe byte), group signalling (`kill -STOP/-KILL -pgid`), and `getsid`
  batch observation.

## Design sketch

1. **Move the mechanism into the C helper, on every OS.** The Windows branch
   of `scripts/bootstrap/bootstrap-session-exec.c` (`--supervise`, landed
   2026-09-24) already owns the whole lifecycle: it creates the session (a Job
   Object), starts the workload suspended and admits it, samples RSS, and handles
   the cap, timeout and interrupt kills, the quiescence check and a stats file.
   Add the same `--supervise` mode for POSIX: `fork` + `setsid` + gate, per-tick
   `/proc/<pid>/stat` (Linux), `libproc`/`sysctl` (macOS, reusing
   `macos-process-observer.c`) or `kvm_getprocs` (FreeBSD), then STOP/KILL
   quiescence. The helper is a sanctioned C bootstrap boundary; it needs a
   Simple twin under the pure-Simple HAL policy
   (`doc/07_guide/os/hal/pure_simple_hal.md`).
2. **Replace the Perl front end with `.shs`.** A `process-tree-rss-guard.shs`
   (a) resolves and hash-checks the cached helper (same key: source sha +
   compiler identity + flags + target, `.sha256` sidecar, atomic publish),
   (b) writes the argv spec file (NUL-separated, via `printf '%s\0'`),
   (c) runs `helper --supervise`, and (d) renders the receipt from the stats
   file with the same keys the Perl version writes today. Nothing
   time-critical stays in the shell, so no per-sample fork is needed.
3. **Simple twin for the post-bootstrap lane.** Once a trusted
   `bin/release/<triple>/simple` exists, `src/app/` gets a pure-Simple
   supervisor with the same receipt contract, driving the same helper through
   SFFI. The `.shs` stays the bootstrap-time entry, and the Simple twin becomes
   the default for `simple test` and the other tooling.
4. **Parity gate.** `test/01_unit/scripts/process_tree_rss_*` runs against
   both front ends. The receipt key sets must be byte-identical, and the
   kill-on-cap / timeout / interrupt / quiescence verdicts must match.

## Acceptance

- `process-tree-rss-watchdog.pl` is deleted, and no bootstrap path invokes `perl`
  for RSS guarding.
- The same receipt contract holds on Linux, macOS, FreeBSD and Windows, including
  `exit_status` crash classification as 128+signal. On Windows, NTSTATUS is
  mapped by the helper (`ntstatus_to_posix`).
- Warm guard start is no slower than the Perl version. Measured Windows
  baseline 2026-09-24: ~210 ms warm, cached helper.
