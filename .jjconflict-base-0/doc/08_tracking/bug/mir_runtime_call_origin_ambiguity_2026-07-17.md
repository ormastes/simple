---
id: mir_runtime_call_origin_ambiguity_2026-07-17
status: PARTIALLY-RESOLVED
severity: blocking
discovered: 2026-07-17
discovered_by: high-level review of runtime/local collision fix
related: doc/08_tracking/bug/codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12.md
related: test/fixtures/compiler/native_runtime_generic_call_origin_collision_repro.spl
---

# MIR cannot distinguish source calls from compiler-generated runtime calls

Both pure-Simple and Rust MIR currently encode a named source call and a
compiler-generated runtime helper call with the same string-shaped target.
Name-only local precedence can therefore redirect generated allocation or
collection calls into an unrelated user body.

## Exact reproducer

`test/fixtures/compiler/native_runtime_generic_call_origin_collision_repro.spl`
defines local `rt_array_new` and `rt_array_push` bodies, then constructs a
function-valued array literal. That lowering path emits named runtime calls
(unlike the dedicated scalar `ArrayLit` instruction). The literal must still
use runtime allocation/push while an explicit source call must reach the local
body. Correct output is `2` then `99`; the current MIR cannot express both
ownership choices, so the fixture is not in a green executable gate.

## Prevention until fixed

`scripts/check/check-bootstrap-portability.shs` rejects new definitions of a
selected high-risk set of allocation/container helper names in `src/compiler`,
`src/app`, or `src/lib`. It is a containment guard, not a substitute for call
origin. Existing inline length/get/set helpers are separately protected by the
passing collision fixture.

## Required fix

Add explicit Source versus Runtime call origin to pure-Simple MIR first, carry
it unchanged through optimizers, interpreters, serialization, LLVM, and
Cranelift, then mirror the model in Rust MIR. Runtime imports and mangled local
bodies with the same spelling must coexist. Promote the reproducer to the AOT
gate only after it prints exactly `2\n99\n` on LLVM and Cranelift.

## Resolution (2026-07-17, partial)

**Coordinator decision point (not yet made -- read before closing this
doc):** the shipped mechanism (below) is inert for every module that does
NOT define a local `rt_array_new`/`rt_array_push` -- `llvm_function_symbol_name`
returns the name unchanged, so nothing that builds today changes at all.
It only activates for a genuine name collision, which was ALREADY a loud
build failure (type-conflicting `declare`/`define`, verified below) or
lint-banned in owned code. So there is no regression risk to existing
programs. BUT within that newly-activated collision case, the same
`translate_operand` reroute that correctly sends the fixture's
`rt_array_new(0)` to the local body ALSO catches `.push()`/`.map()`/
`.filter()`'s byte-identical `Const(Str("rt_array_push"))` callee and
sends it to the mangled local body too -- turning that one sub-case from
a loud build failure into a **silent miscompile** (`.push()` calls the
wrong function, no error). That sub-case is narrow (requires the same
lint-banned local collision, and is not exercised by this doc's own
fixture), but "a silent successful build that misbehaves is strictly
worse than a build failure" is stated policy
(`lower_array_lit`'s own comment in `method_calls_literals.spl`).
**Someone with authority to accept that tradeoff needs to explicitly
accept it, or this doc needs to stay open until the real origin
mechanism closes it too.**

**Mechanism shipped: local-definition mangling**
(`src/compiler/50.mir/mir_call_ownership.spl`, `mir_runtime_owned_call_name`
/ `mir_runtime_owned_local_symbol`, `"__simple_local_{name}"`). The
static/unconditional runtime `declare` for `rt_array_new`/`rt_array_push`
(LLVM: `asm_constraints_helpers.spl`; Cranelift: the module-level import
declaration) always claims the bare name. A same-named LOCAL function
definition is now emitted under a private symbol instead of the bare name
(LLVM: `llvm_function_symbol_name` in `_MirToLlvm/class_def.spl`;
Cranelift: `cl_function_emit_name` in `cranelift_codegen_adapter.spl`,
extending the existing len/get/set precedent from the related bug's fix).
Ordinary named-call resolution (`Const(Str(name))`, e.g. an explicit
source `rt_array_new(0)`) is redirected through the same lookup, so it
still reaches the mangled local body. The `AggregateKind.Array`
hardcoded-text lowering (LLVM `aggregate_intrinsics.spl`, Cranelift's
`Aggregate` case) needed no change -- it already targeted the bare
runtime name outside the `Const(Str(...))` machinery entirely; mangling
the local definition is what makes that bare name unambiguous once a
same-named local exists. This fully fixes the doc's exact reproducer
(function-valued array literal + local `rt_array_new`/`rt_array_push`).

**A second mechanism was attempted and reverted; the gap it targeted
remains genuinely open.** `.push()`/`.map()`/`.filter()` on a runtime
array ALSO emit a compiler-generated call to `rt_array_push`/`rt_array_new`,
but via an ORDINARY `MirInstKind.Call` whose callee is a plain
`Const(Str("rt_array_push"))` (`rt_array_push_operand()` and two inline
`rt_array_new` builders in `50.mir/_MirLoweringExpr/method_calls_literals.spl`)
-- byte-identical in shape to a genuine source-level `rt_array_push(...)`
call. Mangling alone does not separate these: an ordinary named call
(mechanism above) and this compiler-generated call now BOTH resolve to
the mangled local symbol when a collision exists, so `.push()` would
silently call the wrong body instead of the runtime. A fix using a
reserved marker prefix on the callee name (`__simple_runtime_call__`,
stripped by the two backends before any local-collision check) was
implemented and verified correct for LLVM and Cranelift specifically --
but the marker is written into MIR at a `50.mir` lowering site that EVERY
backend consumes (interpreter, C backend, native x86_64/aarch64/riscv32/
riscv64 isel, wasm, ...), and only LLVM/Cranelift were taught to strip it.
Concretely checked: `95.interp/mir_interpreter.spl`'s `Call` handling
resolves the callee by exact string lookup in `function_table` and
silently zeroes the destination on a miss (no error); the C backend
(`_CBackendTranslate/instruction_lowering.spl`) emits the callee text
verbatim as a C function call, which would become a call to an
undeclared/nonexistent C symbol. Native isel and wasm were not checked in
detail but were not confirmed safe either. Since `mir_interpreter.spl` is
NOT part of the live `bin/simple run`/`native-build` path (only reachable
from two isolated unit/system tests, neither of which uses
`.push()`/`.map()`/`.filter()`) the interpreter risk is low in practice,
but the C backend and other native targets were not similarly cleared,
and shipping a change to shared lowering that only 2 of N consuming
backends handle is not an acceptable trade for closing a gap that is
already narrow (requires an actual local `rt_array_new`/`rt_array_push`
collision, which `check-bootstrap-portability.shs` bans in
`src/compiler`/`src/app`/`src/lib`) and not exercised by this doc's own
fixture. The marker mechanism was fully reverted;
`method_calls_literals.spl` is back to its pre-fix content byte-for-byte
(`git diff` empty). `mir_call_ownership.spl` documents the gap and the
reason it was left open ("KNOWN OPEN GAP" section) so it isn't
rediscovered from scratch.

**Verified (LLVM):** the pure-Simple LLVM backend (`compiler.backend.MirToLlvm`)
was driven directly with a hand-built `MirModule` (local `rt_array_new`
returning 99, local `rt_array_push` returning 98, an ordinary call
`rt_array_new(0)`, and an `Aggregate(Array)` instruction) via
`translate_module`.

Before the fix (raw output, invalid IR):
```
declare ptr @rt_array_new(i64)
...
define i64 @rt_array_new(i64 %l0) {   ; TYPE-CONFLICTING with the declare above
  ret i64 99
}
```
After the fix:
```
declare ptr @rt_array_new(i64)
declare i8 @rt_array_push(ptr, i64)
define i64 @__simple_local_rt_array_new(i64 %l0) { ret i64 99 }
define i64 @__simple_local_rt_array_push(i64 %l0, i64 %l1) { ret i64 98 }
define i64 @__simple_main() {
  %l10 = call i64 @__simple_local_rt_array_new(i64 0)   ; source call -> local
  %l11 = call ptr @rt_array_new(i64 2)                  ; array literal -> runtime
  call i8 @rt_array_push(ptr %l11, i64 7)
  call i8 @rt_array_push(ptr %l11, i64 8)
  ret i64 %l10
}
```
Permanent regression coverage:
`test/01_unit/compiler/backend/llvm_runtime_call_origin_spec.spl` (3 `it`
blocks: no bare-symbol `define`/mangled-local `define` present + static
`declare` unambiguous, ordinary source call resolves to the mangled
local, array-literal lowering stays on the runtime symbol). The exact
construction code in that spec was executed directly in-session via
`bin/simple run` on an extracted copy and produced the output shown
above; the spec itself could not be executed through `bin/simple test` in
this session (unrelated pre-existing breakage: the test-runner harness
fails to resolve `rt_cli_arg_count` before reaching any spec content --
reproduces on pre-existing specs too, e.g.
`llvm_call_arity_reconcile_spec.spl`).

**Cranelift:** `cl_function_emit_name` received the mirrored mangling
edit (same shared `mir_call_ownership.spl` helper). Verified to
parse/type-check (`cranelift_codegen_adapter.spl` compiles cleanly under
`bin/simple run` of a probe that imports it and exercises the shared
helper functions with the expected results) and verified NOT to have
regressed the existing `cranelift_aggregate_runtime_abi_spec.spl` gate --
every one of its ~30 substring/ordering assertions was extracted into a
standalone script and re-run in-session against the current file content;
all passed. **Not** verified to actually codegen correctly end-to-end --
`bin/simple native-build` fails on an unrelated pre-existing error
(`unknown property or method 'body' on String`) even for a trivial `fn
main() -> i64: 0` probe in this session's repo state, so the doc's own
promotion bar ("prints `2\n99\n` on LLVM and Cranelift") is **not yet
met** for either backend via the real CLI path -- only the LLVM MIR
backend's `translate_module` was driven directly and inspected at the IR
text level.

**Rust seed (`src/compiler_rust/compiler/src/codegen/`) intentionally NOT
touched.** `native-build`'s normal path (`bin/simple native-build`) runs
the pure-Simple backend fixed above, not `calls.rs`/`common_backend.rs`;
this doc's own AOT-gate promotion criterion is scoped to LLVM+Cranelift
(pure-Simple), and `check-bootstrap-portability.shs` keeps colliding names
out of the compiler's own source so the Rust seed's bootstrap of the
compiler won't hit this. The seed's `common_backend.rs` already takes a
structurally different approach (a current-module body unconditionally
replaces `func_ids`' entry for its raw name; `call_runtime_1`/`_2` look up
a separate `runtime_funcs` table, never `func_ids`) whose behavior under
this exact collision was not verified here (would require a Rust
recompile + a working native-build pipeline, both out of reach in this
session). Flagged as an open follow-up, not silently skipped.

**Status:** the doc's exact reproducer (array literal + local
`rt_array_new`/`rt_array_push`) is fixed and verified at the IR-text
level on LLVM; Cranelift carries the mirrored fix and passes static
verification but is unexecuted. The `.push()`/`.map()`/`.filter()` +
local-collision gap (a strict superset of what the "Required fix"
section asks for -- real per-call-site MIR origin) remains OPEN;
closing it safely requires either a chokepoint every backend's Call
resolution already routes through (none found) or the real MIR-level
origin field, touching every backend by design. Do not promote the
reproducer to the AOT gate, and do not close this doc, until (a)
`native-build`'s unrelated breakage is fixed and the reproducer actually
runs end-to-end on both backends, (b) the Rust seed side is either
confirmed unaffected or fixed to match, and (c) a decision is made on
whether the `.push()`/`.map()`/`.filter()` gap needs closing before this
doc can be marked fully RESOLVED (it is out of scope for the fixture but
in scope for the doc's stated "Required fix").
