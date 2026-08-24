# Stage 2 native-build has a hardcoded 300s per-file timeout with no override, so a loaded box fails the bootstrap

**Date:** 2026-08-24
**Status:** OPEN
**Severity:** blocks the bootstrap non-deterministically; the failure is load-dependent, so it reproduces on a busy machine and vanishes on an idle one

## Symptom

A `--strategy=adhoc --full-bootstrap --stop-after-stage2` run aborted at Stage 2:

```
FAILED FILES (1):
  - src/compiler/10.frontend/core/__init__.spl => ...: timeout (300s)
Build failed: native-build aborted: 1 file(s) failed to compile
warning: stage2 native-build failed (exit 1); Stage 3/full CLI unavailable
```

This is **not** a compile error. Nothing is wrong with the source. The single
failing unit is a 665-line re-export barrel (`445` `use`/`export` lines) whose
compile closure is the whole frontend, and it exceeded a wall-clock deadline
while the host was at load ~26 (a concurrent 32-thread `--jobs=full` stage-2,
three agent sessions and seven long-running codex sessions were competing).

## Root cause

Two independent facts combine:

1. `NativeBuildConfig::file_timeout` defaults to **300** seconds
   (`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:537`), and is
   enforced as a hard wall clock per file
   (`.../native_project/compiler.rs:1019-1021`, `rx.recv_timeout(...)` ->
   `Err(_) => Err(format!("timeout ({}s)", timeout_secs))`).
2. The bootstrap driver **never passes `--timeout`**. Verified from the
   committed evidence rather than by reading the script: the Stage 2 command
   transcript records the exact argv, and it contains zero occurrences of
   `timeout`:

   ```
   native-build --target x86_64-unknown-linux-gnu --backend llvm \
     --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
     --source src/lib --entry-closure --threads 32 --cache-dir ... \
     --mode dynload --entry src/app/cli/bootstrap_main.spl --runtime-path ... -o ...
   ```

So every Stage 2 on every host is pinned to 300s per file.

## Why the obvious workaround does not work

`SIMPLE_TIMEOUT_SECONDS=0` does **not** help and must not be quoted as a fix.
It is read by the *driver* wall-clock path
(`src/compiler_rust/driver/src/cli/init.rs:267-271`) and by examples-safety; it
has no connection to `NativeBuildConfig::file_timeout`. Exporting it before the
bootstrap — which this session did — changes nothing about this failure.

The seed CLI *does* accept `--timeout=<n>` (`native_build_sffi.rs`, the
`--timeout=` prefix branch, feeding `file_timeout: timeout`). The flag exists
and is wired; the bootstrap driver simply never uses it.

## Why this is a real defect and not just "the box was busy"

A per-file deadline that cannot be raised makes bootstrap success a function of
whatever else happens to be running on the host. The same tree bootstraps on an
idle machine and fails on a loaded one, with an error (`timeout (300s)`) that
reads like a compiler hang rather than a scheduling artifact. That is a
fail-closed-at-the-wrong-layer problem: the deadline is protecting against a
genuine hang, but with no escape hatch it also rejects legitimately slow work.

## Fix (not yet applied)

Pass a configurable timeout from the driver, defaulting to the current 300 so
behaviour is unchanged unless asked, e.g.
`--timeout="${SIMPLE_BOOTSTRAP_FILE_TIMEOUT:-300}"`.

**Trap for whoever implements it:** the Stage 2 argv is hash-coupled. The real
invocation (around `scripts/bootstrap/bootstrap-from-scratch.sh:6025-6032`) and
the `bootstrap_stage3_args_sha256` computations (around `:3501-3507` and
`:3512-3518`) must be changed **together and identically**, or the recorded
args digest stops matching the executed command and stage admission fails.
There is more than one such args-hash site; grep `--threads` to enumerate them
before editing.

## Workaround used in this session

Re-ran Stage 2 with `--jobs=half` (16 instead of 32) once the competing load
had dropped, to reduce per-file wall time by lowering self-contention.
