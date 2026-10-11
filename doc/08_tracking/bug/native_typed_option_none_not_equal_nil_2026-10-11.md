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

## Follow-up: optional parameter is boxed again (2026-10-11)

After replacing the local guards with `trace.?`, the native fixture reached
`CompilerInventoryTraceV1.captured_pointer` on the absent trace and crashed
in `spl_str_slice`/`strlen`. GDB showed its receiver word equal to the empty
pointer/digest/membership text argument word, rather than a valid trace
instance. The call from `_compiler_inventory_refresh_owned_v1` to its
optional-trace callee emitted `rt_enum_new` around an already boxed `None`.
The outer `Some(None)` passes presence checks and then exposes the inner
absent value as the method receiver.

`MirLowering.lower_function_with_gpu_metadata` records each parameter's
HIR type but did not mark an `Optional` parameter as an existing canonical
Option handle. The generic call argument path therefore applied
`ensure_option_handle` again when that parameter was forwarded. The source
candidate now records optional parameter locals in `option_value_locals` and
marks their runtime representation. A focused MIR probe and a separate
native forwarding fixture are authored; executable verification remains
pending. The initial 356-module MIR probe timed out at 300 seconds. The
synthetic-HIR revision reduced the closure to 331 modules, but its wrapper
also timed out at 300 seconds; the orphaned worker then stayed at HIR 167/331
on `compiler.frontend.core._AstExpr.accessors` with full CPU for over a
minute and was terminated under the repository runaway guard. No executable
MIR assertion passed.

The one-module forwarding fixture compiled and ran with the older admitted
Stage 2 compiler. It exits 1 with
`OPTIONAL_FORWARD_NONE_BECAME_SOME`, a concrete red baseline for the
compiler-source repair. That binary predates the new parameter-provenance
mark, so this result does not validate the repair. The other available
`bin/simple` identifies itself as the Rust seed and is not an allowed
fallback. The Stage 2 binary's public command path does not run arbitrary
source fixtures.

Crash evidence: `build/mini_builds/target6_tracked_move_refresh_probe/gdb_segv.log`
and `gdb_trace_call.log` in the isolated worktree.
