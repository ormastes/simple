---
id: mir_runtime_call_origin_ambiguity_2026-07-17
status: OPEN
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
