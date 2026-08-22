# Pure-Simple native MCDP focused check/test SIGSEGV

## Status

Open.  The retry budget is exhausted: do not run either reproducer again in
the originating MC/DC verification session.  Resume only in a fresh,
crash-capturing process after the compiler identity below has been admitted.

## Frozen evidence

- Source revision: `76193ab4953a3157e7d6d211f2bc10159107f026`
  (`docs(mcdc): record performance hardening evidence`).
- Candidate executable:
  `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
- SHA-256:
  `969fec3898b606ddffbfb629e1e427d086fb46448dfbea6a7caad287f260aedd`
- ELF build ID: `904d6cef2a352e61b0278b3cfcc9d93b36a847b0`.
- Size: 60,415,648 bytes; inode 225216445; mtime
  `2026-08-22 01:01:53.486471860 +0000`.
- Host/target: Linux x86-64, pure-Simple release executable with debug info.
- Kernel evidence, first attempt at 2026-08-22 05:54:00 UTC:
  PID 2967971, SIGSEGV read at address `0x11`, instruction pointer
  `libc.so.6` ELF offset `0x18b95d`.
- Kernel evidence, second attempt at 2026-08-22 05:54:07 UTC:
  PID 2968490, SIGSEGV read at address `0x1b`, the same libc offset.
- The installed libc debug map resolves offset `0x18b95d` to
  `__strlen_avx2` (`strlen-avx2.S:76`).
- Both invocations returned shell status 139.  Apport retained no matching
  report or core, and no command transcript was retained under `build/` or
  `/tmp`; therefore there is no trustworthy caller frame.

## Reproducer scope

The two failing focused operations were the check/test of
`test/01_unit/compiler/driver/native_mcdc_transport_spec.spl` introduced with
the native `<artifact>.mcdp` companion transport.  Preserve their exact CLI
arguments from the calling session when available.  A fresh-session capture
should run each operation at most once, with core capture enabled, and must
record the resolved executable identity before execution.

Do not replace this with a Rust-seed run: seed behavior is diagnostic only and
cannot admit the pure-Simple compiler or this feature.

## Classification

Earliest proven boundary: an invalid low-valued pointer reached libc `strlen`
during the pure-Simple focused compiler operation.  Repetition at the same
instruction with different low addresses (`0x11`, `0x1b`) establishes a
deterministic invalid-text-pointer class, but not its owner.  The evidence does
**not** distinguish parser/HIR text corruption, an extern text-ABI mismatch,
or an earlier lifetime error.  Assigning the fault to the new streaming writer
would be speculation because no caller stack exists.

No source fix is safe from this evidence alone.  In particular, changing the
manifest format, reducing its 64 KiB reusable buffer, or weakening atomic
publication would hide the failure without proving its cause.

## Fresh-session capture and unblock

1. Copy or otherwise pin the exact executable above before any deployment can
   replace its inode, and verify its SHA-256/build ID.
2. Enable a recoverable core destination for the one-shot process; record the
   exact command, environment allowlist, source revision, target, mode, elapsed
   time, and maximum RSS.
3. Obtain `thread apply all bt full` plus registers and mappings in GDB using
   this unstripped executable and the host libc debug symbols.
4. Classify the first non-libc frame.  If it is an extern call, compare its MIR
   text expansion and C symbol prototype; if it precedes execution, reduce the
   imported module/construct while preserving the crash.
5. Add the minimized case as a compiler regression and fix the smallest owner.
   Rerun only the failed shard, once, then the focused MCDP operation once.

Unblock condition: a symbolized first non-libc frame or a minimized source case
that identifies the corrupt text producer, followed by a focused passing
pure-Simple check/test on a recorded admitted compiler identity.  Until then,
native MCDP Simple execution and its performance evidence remain unverified.
