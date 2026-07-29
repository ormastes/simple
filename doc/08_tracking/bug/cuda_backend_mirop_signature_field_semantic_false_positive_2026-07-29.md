---
id: cuda_backend_mirop_signature_field_semantic_false_positive_2026-07-29
status: OPEN
severity: medium
discovered: 2026-07-29
discovered_by: lane CUDA1 (cuda-symbolid-layout) while running test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl
related: test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl
related: src/compiler/70.backend/backend/cuda_backend.spl
---

# `emits direct device calls by symbol name` fails with a false `MirOperand has no field named signature` semantic error

## Symptom

Running `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`
(the CUDA backend intensive MIR contract suite) always fails one example:

```
✗ emits direct device calls by symbol name
    semantic: class `MirOperand` has no field named `signature`
```

The other 9 examples in the same file pass, including two new ones added by
lane CUDA1 that exercise a completely unrelated code path (Struct(SymbolId)
field-layout resolution). This failure is **pre-existing** and unrelated to
the CUDA1 change: it reproduces identically before and after CUDA1's edits to
`cuda_backend.spl` (confirmed by re-running after reverting a keyword-naming
mistake CUDA1 introduced and fixed separately — the failure persisted
unchanged).

## Suspected cause

The failing test (`test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl:79-97`)
builds a direct-call `MirOperand` via
`MirOperand(kind: MirOperandKind.Const(MirConstValue.Str("cuda_add"), MirType(kind: MirTypeKind.FuncPtr(callee_signature))))`
and a `MirInstKind.Call(...)` instruction. Neither `MirOperand` nor any of its
variants declare a field literally named `signature` — `cuda_backend.spl`'s
own `func.signature` accesses are on `MirFunction`, not `MirOperand`. This
looks like a false positive from whatever static/semantic checker runs ahead
of test execution (test-runner "semantic:" pre-check, not a runtime
assertion failure) — plausibly confused by the `FuncPtr(signature: MirSignature)`
payload name inside `MirTypeKind` while resolving a field access chain
through `Const(_, ty)` -> `ty.kind` -> `FuncPtr(signature)`, and misattributing
the payload binding name `signature` as a field expected on `MirOperand`
itself.

## Scope note

Not fixed as part of lane CUDA1 (cuda-symbolid-layout): the failure is in the
`compile_direct_call`/semantic-check path, which CUDA1 did not touch (CUDA1's
changes were confined to `field_layout`, `compile_aggregate`, `compile_gep`,
and the new `cuda_can_size`/`cuda_type_size`/`cuda_type_align` family). Root
cause needs someone with context on the test-runner's static "semantic:"
pre-check (likely in the compiler's semantic-analysis pass, not
`cuda_backend.spl`).
