# Interpreter's `rt_process_is_running` returns false for any pid it did not spawn

Date: 2026-09-06
Status: FIXED IN SOURCE — awaiting a seed deploy
Area: `src/compiler_rust/compiler/src/interpreter_extern/system.rs`

## Symptom

`cs`'s agent roster showed every launched agent as dead:

```
AGENTS (1)
  > 1 a1  caret  exited: pane pid 342355 is not running
  status exited: pane pid 342355 is not running
```

while `tmux list-panes` on the very same pane said the opposite:

```
pane=%26 pid=342355 dead=0
```

The agent was alive the whole time. The left control panel was simply lying
about it.

## Root cause

The interpreter's extern consulted only `SPAWNED_PROCESSES` — the map of
children *this* process spawned — and returned `false` for anything absent:

```rust
match processes.get_mut(&pid) {
    Some(child) => ...,
    None => Ok(Value::Bool(false)), // not tracked
}
```

A tmux pane's process is spawned by **tmux**, not by `cs`, so it is never in
that map, and the answer was unconditionally `false` no matter how alive the
process was.

The C runtime already had this right —
`src/runtime/runtime_process.c:54` does `waitpid(WNOHANG)` and, on `ECHILD`
(meaning "not my child"), falls back to `kill(pid, 0)`. So the two
implementations of the same extern disagreed, and the weaker one is the one the
seed uses.

This is the same shape as the other seed findings this session
(`seed_interpreter_stdin_read_line_erases_eof_2026-09-06.md`): **the interpreter
extern is a degraded reimplementation of a C runtime function, and returns a
confidently wrong value rather than failing.**

## Fix

`None` now falls through to a `kill(pid, 0)` liveness probe, matching the C
runtime. `EPERM` counts as alive — the process exists but is owned by another
user; treating that as dead is precisely the bug. Non-unix reports `false`
rather than claiming liveness it did not verify.

## Verified

Same `cs` session, same command, only the binary differs:

| binary | roster |
|---|---|
| current `bin/simple` | `> 1 a1  caret  exited: pane pid ... is not running` |
| privately rebuilt seed | `> 1 a1  caret  running` |

with `tmux list-panes` reporting `dead=0` in both cases — i.e. the process was
alive both times and only the fixed binary says so.

**`bin/simple` was deliberately NOT replaced** (other sessions are using it, and
this repo has already reverted one seed deploy). Someone must build and deploy
the fixed seed for this to take effect; until then `cs`'s roster keeps
misreporting live agents as exited.

## Note for whoever takes the deploy

Three interpreter-extern fixes now sit in source awaiting the same rebuild —
this one, the EOF erasure, and the `rt_atexit_install`/`rt_signal_install`
bridge. They should ship together.
