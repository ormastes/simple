# Native typed Option `None` is unequal to `nil`

Status: OPEN (2026-10-11). Affects the SCV inventory trace guard in the
focused tracked-move native fixture.

`inventory_trace_create_v1("")` returns `nil` as
`CompilerInventoryTraceV1?`. In the no-stub, core-C native fixture,
`if trace != nil` entered the branch and `trace!` called `rt_panic` with
"called `!` force-unwrap on a nil Option". The native disassembly compared
the boxed `None` pointer directly with raw nil value `3`, while
`rt_is_some` correctly reported false for the same value. GDB captured
`trace` as a tagged pointer ending in `...e1` at the panic.

The SCV bridge now uses `if trace.?` for its optional trace class so the
guard follows the native Option presence predicate. This is a local repair;
the language-level equality bug still needs a focused native and interpreter
regression, then a compiler/runtime fix that makes `None == nil` true for a
typed Option without changing equality for other enums.

Evidence: `build/mini_builds/target6_tracked_move_refresh_probe/gdb_panic.log`,
`gdb_panic2.log`, and `owned_trace_guard_disas.log` in the isolated worktree;
the backtrace identifies the owner, and the object disassembly confirms the
raw comparison. The fixture has not yet completed its V4 warm path.
