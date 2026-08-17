# `rt_process_wait` discards the signal number of a killed child

- **Filed:** 2026-08-17
- **Status:** OPEN (worked around, not fixed)
- **Domain:** runtime / process
- **Severity:** P2 — silently collapses every distinct process death into one
  indistinguishable value

## Symptom

`rt_process_wait(pid, timeout_ms)` returns **-1** for a child that died by a
signal, for every signal. SIGSEGV, SIGKILL/OOM and SIGTERM are indistinguishable
from each other and from a generic runtime error.

Measured directly on this host (`bin/simple run`, seed binary):

| argv passed to `rt_process_spawn_async("/bin/sh", …)` | status |
|---|---|
| `["-c", "kill -SEGV $$"]` | **-1** |
| `["-c", "kill -TERM $$"]` | **-1** |
| `["-c", "kill -KILL $$"]` | **-1** |
| `["-c", "/bin/sh -c \"$0\"\nexit $?", "kill -SEGV $$"]` | 139 |
| `["-c", "/bin/sh -c \"$0\"\nexit $?", "kill -TERM $$"]` | 143 |
| `["-c", "/bin/sh -c \"$0\"\nexit $?", "kill -KILL $$"]` | 137 |

## Cause

`src/compiler_rust/runtime/src/value/sffi/env_process.rs:990` (and the
indefinite-wait branch just above it):

```rust
Ok(status) => status.code().unwrap_or(-1) as i64,
```

On Unix `ExitStatus::code()` is `None` precisely when the child was killed by a
signal. `.unwrap_or(-1)` therefore throws away the one piece of information the
caller needs. `std::os::unix::process::ExitStatusExt::signal()` carries it and is
not consulted.

## Why it matters

`doc/02_requirements/compiler/supervised_builder.md` R2 requires the supervisor to
separate CRASHED (a genuine compiler defect) from TERMINATED (an external SIGTERM
— on this host `earlyoom` runs `--prefer ^(simple|...)` and actively SIGTERMs
`simple`, so this is the *most likely* status a real build sees under load).
Collapsing both to -1 makes that distinction unrepresentable, and an
infrastructure kill then reads as a compiler bug. That is exactly the class of
phantom defect the requirement exists to prevent.

## Workaround in place

`parallel_supervised_argv()` in
`src/compiler/80.driver/driver_build/parallel.spl` interposes a supervising
shell so the unit runs one level down (`/bin/sh -c "$0"`). The middle shell is
not the process that dies, so it survives, `wait(2)`s the unit, and re-reports
128+N as its own ordinary exit code. Note that the naive `"<cmd>; exit $?"` form
does **not** work: if the unit dies, the shell running it is the process that
dies, and a dead shell never reaches its next statement.

Cost: one extra `fork` + `execve` per build unit, and the workaround only helps
callers that remember to use the wrapper. Any other `rt_process_wait` caller in
the tree is still blind to signals.

## Fix

Return the signal as `128 + signal()` when `code()` is `None`, matching the
shell convention the rest of the tree already decodes
(`build_outcome_classify_status` in
`src/compiler/80.driver/driver_build/build_outcome.spl`). Then delete the
wrapper. `runtime_process.c`'s implementation should be checked for the same
defect at the same time.

## Evidence / regression

`test/01_unit/compiler/driver/supervised_build_survives_worker_death_spec.spl`
spawns real children that really die. Ablating `parallel_supervised_argv()` back
to `["-c", inner_cmd]` turns 2 of its 4 examples red (`expected [] to contain
oom.spl`), which is the direct proof that the runtime, unaided, cannot see the
signal.
