# Typed indirect calls cannot yet certify exact ORC ABI adapters

Status: source-audited prerequisite blocker; no runtime reproduction attempted.
Scope: the inspected pure-Simple HIR-to-MIR indirect-call path and canonical
dynamic-call surfaces. This is not a claim that every native call mechanism is
missing. The scalar ORC tests-first branch remains incomplete.

## Concrete lowering gap

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:5138` reads
`HirTypeKind.Function(params, _, _)` into `call_param_types`, but the subsequent
indirect-call path at lines 5312–5320 creates a fresh MIR parameter list by
pushing `MirType.i64()` for every argument. It sets return type by lowering the
callee's entire type, rather than extracting the function's declared result.
The resulting signature feeds both the raw indirect call and closure branch.
Consequently a source function-pointer annotation alone cannot establish an
exact pointer/i32/void C call through this route.

MIR itself has the needed expressive surface: `mir_data.spl:673` emits
`CallIndirect` with an explicit `MirSignature` and no destination for Unit.
`src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:458`
uses signature parameter types, converts operands accordingly and selects the
result type from the destination/signature. This shows a repair seam, not
executed ABI correctness. The backend cannot recover types erased upstream.

## Why existing dynamic wrappers do not close it

`std.nogc_sync_mut.sffi.dynamic.DynI64FnSlot` explicitly admits only
`i64(i64...)` for up to eight arguments. `runtime_native.c:8795` implements
that shape using i64 C function-pointer typedefs. Presence, argument count and
live-provider checks do not make that call pointer-returning, void-returning
or i32-returning. The existing llvm_loader generic integer calls use this same
assumption. A new wrapper around them would not provide exact ABI evidence.

Raw allocations and pointer reads/writes exist, but they address storage only.
They cannot change the callee prototype or repair a function result register
contract. The narrow output-byte helper has its own fixed i64-return signature,
not LLVMParseIRInContext's i32 status and two independent pointer outputs.

## Required test-first repair before ORC source

Preserve the declared function parameter and result types in the indirect-call
MIR signature, including pointer, i32 and Unit cases. Make raw foreign function
pointers distinguishable from closure handles before routing through a closure
probe. Require the platform C calling convention and an unsafe owner boundary;
do not infer ABI validity from pointer/integer width equality.

Independent source-to-HIR-to-MIR-to-LLVM tests must assert exact pointer/i32/void
call signatures, output-pointer stores and no fabricated result for void. Then
an admitted native runner must invoke known exact-signature providers and check
nonzero/zero results and output writes. Missing symbol, invalid signature and
retired mapping must fail before invocation. No C/Rust source changes, ABI cast
workarounds or foreign invocation were made during this investigation.

Even after this repair, the ORC session needs its own synchronized identity and
destructor protocol: copied sessions must not retain freed code, and provider
unloading must follow ORC disposal. See
`doc/05_design/collection_scalar_orc_session.md` on the tests-first branch.

## Independent producer/consumer review — 2026-10-03

The consumer-only candidate `d6d5b0a5fbf` is deliberately **not integrated**.
Review found that `lower_lambda_value` in the same lowering file constructs
lifted parameters and results as i64, including noncapturing lambdas represented
as raw function pointers. Changing only indirect callers to pointer/i32/Unit
therefore creates incompatible producer/consumer signatures. Tests which accept
a callback parameter without constructing a lambda cannot catch this mismatch.
The eventual repair must test actual capturing and noncapturing producers,
their call sites, and runtime collection helpers which use the flat-word ABI.
REQ-002 execution prerequisites still apply; source inspection is not parity.

The closure probe itself has a narrower, existing safeguard: in
`src/runtime/runtime_native.c`, `rt_core_as_closure` checks tag and pointer-only
registry membership before dereferencing, explicitly handling raw code-pointer
tag collisions. Thus an absent safe discrimination check is not established by
this audit. That check still does not authenticate a raw target's signature or
lifetime. No foreign function was invoked during this review.
