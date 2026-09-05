# `rt_process_wait` discards the signal number of a killed child

- **Filed:** 2026-08-17
- **Status:** FIXED 2026-08-17 (Rust runtime + C runtime), verified by execution on a
  freshly built, non-deployed seed. See the note at the end. Workaround removal pending redeploy.
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

## 2026-08-17 — FIXED

`exit_status_to_code()` was added to `src/compiler_rust/runtime/src/value/sffi/env_process.rs`
(returns `code()` when present, else `128 + ExitStatusExt::signal()` on Unix, else -1) and
every `.code().unwrap_or(-1)` site in that file — including both `rt_process_wait` branches
— now routes through it. The C runtime had the same defect: `rt_process_wait` in
`src/runtime/runtime_process.c` returned -1 for `!WIFEXITED`; it now returns
`128 + WTERMSIG(status)` on `WIFSIGNALED` in both the blocking and polling branches.

Repro/verification (probe spawns via `rt_process_spawn_async` and waits, no supervising
shell — i.e. the workaround is NOT in the path):

```
$ env SIMPLE_RUST_SEED_WARNING=0 bin/simple run wait.spl        # deployed pre-fix seed
SEGV=-1
TERM=-1
KILL=-1
$ env SIMPLE_RUST_SEED_WARNING=0 /mnt/data/cargo-bugfix-0dc8/release/simple run wait.spl
SEGV=139
TERM=143
KILL=137
```

C-runtime gate: `sh scripts/check/check-c-runtime-compiles-push.shs` ->
`PASS — 104 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)`.

Binary: /mnt/data/cargo-bugfix-0dc8/release/simple (built 2026-08-17 13:48, 59554384 bytes, from this worktree's source; NOT deployed to bin/simple).

Not done, deliberately: `parallel_supervised_argv()` in
`src/compiler/80.driver/driver_build/parallel.spl` is left in place. Removing the
wrapper requires the fixed runtime to be the DEPLOYED one; deleting it now would break
every build running on the current `bin/simple`. Delete it after the seed redeploy.

**Status:** FIXED (runtime + C runtime), verified by execution on a freshly built,
non-deployed seed. Wrapper removal pending redeploy.

## 2026-08-17 20:1x — RESOLVED on the DEPLOYED seed

Binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (bin/simple), md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45 — the REDEPLOYED seed carrying this session's fixes.

```
$ env SIMPLE_RUST_SEED_WARNING=0 bin/simple run wait.spl
SEGV=139
TERM=143
KILL=137
```

Identical to the isolated-build result (was `-1/-1/-1` on the pre-fix deployed seed).
**Status: RESOLVED.** Follow-up still owed: `parallel_supervised_argv()` in
`src/compiler/80.driver/driver_build/parallel.spl` was kept only until the fixed seed
was deployed — that condition is now met, so the wrapper can be deleted in a separate change.
