# Windows diagnostic child-preflight P3 disposition — 2026-09-22

## Scope

`scripts/check/bootstrap-diagnostic-sweep.shs` delegates every seed compiler
check to an admitted pure-Simple child through `SIMPLE_BINARY` and `SIMPLE_BIN`.
The runner must attribute that child to the runner's repository, preserve paths
with spaces, and publish a terminal diagnostic for every child outcome.

## Confirmed owner/path defect and correction

Before this change, the implicit child was literal `bin/simple`. It was checked
and canonicalized from the caller's current directory. A user could therefore
run the runner from a different worktree containing `bin/simple`; preflight
would succeed, while the run receipt attributed a child unrelated to the
runner's repository.

The implicit child is now derived from the absolute runner path:

```
<absolute runner>/../../bin/simple
```

An explicit `--child-compiler=<path>` remains supported and is canonicalized
after validation. This preserves intentional isolated-artifact use while
preventing an accidental cwd substitution. The failure message now directs the
operator to the explicit override.

The executable reproducer is
`test/02_integration/bootstrap_diagnostic_sweep_test.shs`. It copies the runner
under a fixture directory named `runner repo`, places an executable rogue child
under `rogue cwd/bin/simple`, and asserts that both injected identity variables
are the runner-owned child. It also runs the explicit child from
`child with spaces/explicit simple` and asserts the exact canonical identity.

## Windows disposition

The runner is not Windows-safe as a timeout/process-cleanup owner. Its worker
model requires Perl `fork`, `POSIX::setsid`, negative-PGID `kill`, `/bin/sh`,
and `/bin/sleep`. Those are POSIX process-group semantics; Windows process
groups do not provide equivalent descendant termination. The code also reports
POSIX signals as terminal diagnostic classifications, which has no direct
Windows child-process equivalent.

The MSYS reproduction was:

```
C:\msys64\usr\bin\bash.exe -lc \
  'cd /d/p3-common-windows-mcp-audit && sh test/02_integration/bootstrap_diagnostic_sweep_test.shs'
```

It reached the default-child preflight, then remained live beyond the command's
30.3-second observation window. The active fixture included an MSYS `sh`
process at 12.3 MiB RSS and a Perl observer at 11.1 MiB RSS. It produced no
terminal result receipt. The exact fixture process tree was stopped by PID after
inspection; the test cleanup then started. This is an incomplete Windows run,
not evidence that descendant cleanup succeeded or failed.

## Required Windows owner before enabling this sweep

Implement a Windows-native diagnostic runner (PowerShell or a dedicated Simple
runtime facade) with one Job Object per diagnostic child. The runner must:

1. Start the compiler and delegated child in the job, record the actual PID and
   job identifier, and terminate the job on timeout or parent cancellation.
2. Capture stdout and stderr separately and retain the raw Windows exit code.
3. Classify normal nonzero exit, access violation/abnormal termination, timeout,
   and runner infrastructure failure without inventing POSIX signal numbers.
4. Canonicalize runner-owned and explicit child paths using Windows long-path
   aware APIs, then write those exact paths to the identity receipt.
5. Prove no live job member remains after timeout and parent cancellation.

The acceptance matrix is: normal exit with stdout/stderr; nonzero exit with
stderr; abnormal exit; timeout with a spawned descendant; parent cancellation
with a spawned descendant; default child versus rogue cwd child; explicit child
with spaces; and a long path above the legacy 260-character boundary. Each row
must record elapsed time, peak RSS, child PID/job identity, stdout/stderr byte
counts, raw exit classification, and post-cleanup live-member count.

The portable fixture establishes path selection and the seed environment
binding. Its fake seed records the intended child identity but does not execute
that selected child, so it is not Windows launch evidence.

## Status

The cwd owner/path mismatch is fixed and covered by the portable harness.
Windows process control remains **P3 unresolved** until a Job Object owner and
the matrix above are implemented. Do not invoke this POSIX diagnostic sweep as
Windows evidence.
