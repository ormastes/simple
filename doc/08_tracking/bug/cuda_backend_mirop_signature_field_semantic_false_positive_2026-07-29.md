---
id: cuda_backend_mirop_signature_field_semantic_false_positive_2026-07-29
status: FIXED
severity: medium
discovered: 2026-07-29
fixed: 2026-07-30
discovered_by: lane CUDA1 (cuda-symbolid-layout) while running test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl
fixed_by: lane SIGF (mirop-signature-false-positive)
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

## Root cause (found by lane SIGF, 2026-07-30)

The "semantic:" prefix is misleading — this is not a static/pre-check false
positive at all, it is a **runtime interpreter variable-shadowing bug**, and
`cuda_backend.spl` genuinely triggers it (classification: **(a) real product
bug reachable only when this example runs**, not a checker artifact).

`compile_instruction(builder: PtxBuilder, inst: MirInst, func: MirFunction)`
in `src/compiler/70.backend/backend/cuda_backend.spl` (was line 375) matched
`inst.kind` and, for the `Call` variant, bound the callee payload with the
same name as the method's own `func: MirFunction` parameter:

```
case Call(dest, func, args):
    val call_result = self.compile_call(builder, dest, func, args)
```

`MirInstKind.Call` is declared `Call(dest: LocalId?, func: MirOperand, args:
[MirOperand])` (`src/compiler/50.mir/mir_instruction_kinds.spl:51`) — so the
match-arm payload name `func` is literally a `MirOperand`, colliding in name
with the enclosing method's `func: MirFunction` parameter. The seed
tree-walk interpreter (the engine `bin/simple test` runs on) does not give
this match arm its own scope for the purpose of the caller's binding: after
`compile_instruction` returns, `compile_function`'s own `func` local (up in
its own stack frame, used again at
`func.signature.return_type` for the terminator step, `cuda_backend.spl:225`)
had been silently overwritten by the arm's `func` (the `MirOperand` callee)
whenever the block being compiled contained a `Call` instruction. The next
read of `func.signature` therefore dereferenced `.signature` on a
`MirOperand` value instead of the intended `MirFunction`, producing exactly
`class \`MirOperand\` has no field named \`signature\``. This is the same
family of bug already flagged in a comment a few lines above (`cuda_backend.spl`
~130: "the bootstrap interpreter currently misbinds that payload accessor"),
just recurring at the match-arm level instead of the nested-destructuring
level that comment was originally about.

Confirmed by minimal repro (`CudaBackend.create(...).compile(...)` on the
exact MIR from the failing example) and by the fix below turning the example
green with no other behavior change.

### Fix

Renamed the match-arm payload from `func` to `callee` (matching
`compile_call`'s own parameter name) so it no longer collides with
`compile_instruction`'s `func: MirFunction` parameter:

```
case Call(dest, callee, args):
    val call_result = self.compile_call(builder, dest, callee, args)
```

### Two more pre-existing defects found and fixed while restoring 10/10

Getting the suite to 10/10 (not just the filed example) surfaced two more
bugs in the *first* example ("emits if branches and loop backedges..."),
both pre-existing and unrelated to the `.signature` false positive:

1. **Register-id collision in `PtxBuilder`.** `alloc_reg()` numbers
   temporaries from an internal `next_reg` counter that starts at 0 and is
   never advanced past the fixed MIR-local register ids a function actually
   uses (`reserve_reg_id()` existed in `cuda/ptx_builder.spl` for exactly
   this purpose but was never called from anywhere). A `bool`-typed kernel
   argument's predicate register (`%r0`, from the local's own id) and the
   very first builder-allocated temp (also `%r0`, since `next_reg` was still
   0) landed on the same PTX register name, corrupting the `setp.ne`
   self-comparison. Fixed by calling `builder.reserve_reg_id(local.id.id)`
   for every local at the top of `compile_function` before any temps are
   allocated.
2. **Test asserted an invalid PTX instruction.** The example asserted
   `setp.ne.u8 %r0`, but PTX's `setp` instruction has no 8-bit comparison
   form (valid widths are `.u16/.u32/.u64/.s16/.s32/.s64/.b16/.b32/.b64/.f32/
   .f64` — see PTX ISA `setp` reference); the backend correctly widens the
   `ld.param.u8`-loaded byte into a `.u16` temp before comparing, which is
   the only way to emit assemblable PTX here. Updated the assertion to
   `setp.ne.u16 %r0` to match the (already correct) hardware-legal output.

### Files changed
- `src/compiler/70.backend/backend/cuda_backend.spl` — renamed `Call` arm
  payload `func` → `callee`; added `reserve_reg_id` reservation loop in
  `compile_function`.
- `src/compiler/70.backend/backend/cuda/ptx_builder.spl` — unchanged (the
  already-present `reserve_reg_id` is now actually called).
- `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl` —
  `setp.ne.u8 %r0` → `setp.ne.u16 %r0` assertion fix, with a comment
  explaining PTX's `setp` width constraint.

### Verification
- `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`:
  `Results: 10 total, 10 passed, 0 failed`.
- `test/01_unit/compiler/semantics/param_mutability_semantic_spec.spl`:
  `Results: 4 total, 4 passed, 0 failed`.
