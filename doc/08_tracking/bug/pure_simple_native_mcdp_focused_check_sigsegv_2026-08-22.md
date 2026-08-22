# Pure-Simple native MCDP focused check/test SIGSEGV

## Status

Open.  The retry budget is exhausted: do not run either reproducer again in
the originating MC/DC verification session.  Resume only in a fresh,
crash-capturing process after the compiler identity below has been admitted.

## Frozen evidence

- Source revision: `76193ab4953a3157e7d6d211f2bc10159107f026`
  (`docs(mcdc): record performance hardening evidence`).
- Candidate executable:
  `/mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple`
- SHA-256:
  `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
- ELF build ID: `545d912cac46001892de0d9959e6b0b92497f2b9`.
- Size: 42,477,824 bytes; inode 2259895; mtime
  `2026-08-11 22:10:09.323921115 +0000`.
- Host/target: Linux x86-64, pure-Simple release executable, not stripped.
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

The two failing focused operations were run from
`/mnt/data/worktrees/simple-mcdc-hal`, with
`SIMPLE_LIB=/mnt/data/worktrees/simple-mcdc-hal/src`:

```text
timeout 180 /mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/driver/native_mcdc_transport_spec.spl --mode=interpreter
timeout 180 /mnt/data/worktrees/simple-main/release/x86_64-unknown-linux-gnu/simple check test/01_unit/compiler/driver/native_mcdc_transport_spec.spl
```

Each exited 139.  A fresh-session capture should run each operation at most
once, with core capture enabled, and must record the resolved executable
identity before execution.

Do not replace this with a Rust-seed run: seed behavior is diagnostic only and
cannot admit the pure-Simple compiler or this feature.

## Classification

Earliest proven boundary: an invalid low-valued pointer reached libc `strlen`
during the pure-Simple focused compiler operation.  Repetition at the same
instruction with different low addresses (`0x11`, `0x1b`) establishes a
deterministic invalid-text-pointer class, but not its owner.  Because the
standalone `check` crashes without executing the test or streaming writer, the
first shared failing lane is module loading/parsing/HIR/type checking rather
than MCDP file publication.  The evidence still does **not** distinguish text
corruption in those compiler stages from an earlier lifetime error.  Assigning
the fault to an individual source construct is speculation because no caller
stack or reduced input exists.

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
