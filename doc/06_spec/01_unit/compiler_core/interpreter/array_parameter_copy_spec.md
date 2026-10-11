# Interpreter array parameter copy

Requirement: `REQ-INTERP-ARRAY-PARAM-VALUE`.
Executable: `test/01_unit/compiler_core/interpreter/array_parameter_copy_spec.spl`.

The executable specification calls the production `eval_function_call` with
a real function declaration and then mutates the returned parameter array.
The remaining cases call `val_copy_for_parameter` and the real value arena.
It verifies independent array
storage after append and replacement, independent nested arrays, shared
registered class identities, copied registered value structs with array fields,
unchanged scalar identities plus independent empty arrays, self cycles,
mutual cycles, and repeated child identities.

Both production `eval_function_call` owners (the dedicated call module and
`_EvalOps/call_method_eval`) call this helper. Value structs
recursively use it for their fields, preserving class references while copying
array storage. A reference-owned memo context registers array/struct copies
before visiting their children, preserving cycles and shared subgraphs.
The helper does not replace the general struct copy gate.

## Verification evidence

Release base: `c4cd4530c1d4e61d74ce669d54b9e26c0d625a44`.
Stage 1 cached bootstrap producer SHA-256:
`6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`.

Diagnostic status: **BLOCKED**, declared 7 / executed 0. The explicit AST
owner import encounters the existing `windows_redirected_process.spl`
`Unexpected token: expected Fn, found Colon` parse failure. No assertion
is marked passed, skipped, or weakened. Zero compiler rebuilds.

Pure Simple compiler/core/library/MCP qualification and runtime smokes remain
pending because the release runtime is unavailable on this host. This change
is a draft repair, not a qualified release admission.

## Changed-producer qualification

A separately captured immutable cached producer, SHA-256
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`,
accepts the original full imports on Windows. Its actual host reports
`windows` / `AMD64`; the diagnostic target was pinned to
`windows` / `x86_64` / `x86_64-pc-windows-msvc`.

The final unchanged seven-case specification executed all seven examples:
**6 passed, 1 failed**, zero skipped/dropped, exit 1. The real function parameter
binding case still leaks element replacement: caller element was `9`, expected
`1`. Nested arrays, class identity, struct/array fields, scalar/empty controls,
self cycles, and mutual/shared cycles passed. This is a failing Stage 1 Windows
diagnostic, not native admission. No repair/retry followed this qualification.
The older producer's three blocked cycles remain terminal evidence.

The alternate producer did not honor Linux target overrides in the independent
tiny conditional-import probe. Its result applies only to this pinned Windows
host/target. No projection of the original library imports was used.

## Duplicate function binder repair

A new, bounded investigation identified a separate missed production binder.
Temporary entry instrumentation selected `_EvalOps/call_method_eval.spl`, whose
parameter assignment still bound the caller value directly. The unchanged
first case returned arena ID 263 for both caller and parameter, with no new
arena allocation. The dedicated `eval_calls.spl` binder was not selected by
this cached producer's flat symbol dispatch. Instrumentation was restored
before the repair.

Both function binders now use the canonical `val_copy_for_parameter` helper.
The helper also imports its array and struct mutation owners explicitly.
The focused first case, preserving every original assertion, executed once
with authoritative example counters after this repair: **1 passed, 0 failed,
0 skipped/dropped**, exit 0. Caller ID 263 and copied ID 264 differ; append and
element replacement leave the caller's length 2 and first element 1. The six
already-green helper cases were not replayed. No compiler rebuild occurred.
Evidence: `build/phase1-array-binding-cause-20261011/repaired-binding-direct.log`
and `evidence.json` in the shared workspace.

This remains a Stage 1 Windows bootstrap diagnostic with producer SHA-256
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
The original seven-case failing receipt is retained as historical evidence;
no full-suite PASS at the repaired head is claimed. Pure Simple runtime
qualification remains pending, so the PR remains draft.

The regression disables JIT through the real `jit_init(999999, 0)` owner.
Both compiled fast paths precede parameter binding and pass non-integer
arena IDs directly. The current `jit_try_execute` owner returns placeholder
0 for compiled entries, so this result does not qualify compiled/JIT execution.
That separate existing limitation is not the cause of this tree-walk failure.