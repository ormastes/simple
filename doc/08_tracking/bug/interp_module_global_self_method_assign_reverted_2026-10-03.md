# Interpreter reverts `g = g.method()` on a module global (2026-10-03)

**Status:** fixed in source (seed interpreter), regression spec
`test/01_unit/compiler/interpreter/module_global_me_method_assign_spec.spl`.

## Symptom
Inside a module function, `_svc = _svc.add_client(att)` (module `var`, method
called on the same var, result assigned back) is invisible to every later call
— under the interpreter only. `simple run` (JIT) is correct. smux attach/detach
and pane close reported success and changed nothing under `simple test`.

Minimal repro (interpreter `0`, JIT `1`):

```simple
class Box:
    n: int
    me bump() -> Box:
        return Box(n: me.n + 1)
var _st: Box = Box(n: 0)
fn plain_write():
    _st = _st.bump()
```

`_st = Box(n: _st.n + 1)` and `var s = _st; s = s.bump(); _st = s` were both
correct.

## Cause
Module globals live in two stores: the flat `MODULE_GLOBALS` map and the
per-module owner store (`set_owned_global`), which a function frame snapshots
and republishes on exit. The receiver path
(`interpreter_helpers/patterns.rs` `handle_method_call_with_self_update`)
removes `_st` from the frame (leaving a deleted marker) and syncs the OLD
receiver into both stores. The assignment then saw `!env.contains_key(name)`
and wrote the new value into the flat map only (`interpreter/node_exec.rs`).
On function exit the owner store — still holding the old receiver — was
republished, reverting the assignment.

## Fix
`node_exec.rs`: the flat-only branch now calls `sync_flat_global`, which writes
both stores.

## Related defect found in the same session
Windows `rt_process_read_stdout` (interpreter, `interpreter_extern/system.rs`)
blocked forever when the piped child had nothing pending: POSIX sets
`O_NONBLOCK`, Windows anonymous pipes have none. Fixed by asking
`PeekNamedPipe` for the pending byte count and reading only that.
`rt_pty_is_running` was implemented but never registered in the interpreter
extern table; registered.
