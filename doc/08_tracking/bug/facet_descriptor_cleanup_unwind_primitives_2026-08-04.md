# Facet descriptor cleanup lacks portable throw/unwind primitives

Date: 2026-08-04

## Problem

A `FacetRef` owns an exact-generation descriptor lease that must be released on
every edge leaving its lexical scope. MIR lowering can insert cleanup on normal
CFG edges, explicit return/error propagation, loop transfer, and aborting panic,
but it cannot represent portable cleanup for language `throw`, async task
cancellation, or a foreign exception crossing a call.

`HirExprKind.Throw` exists, but MIR has no throw/resume terminator and the normal
lowerer emits no `MirTerminator.CallTerminator`. `CallTerminator` has an optional
unwind target, yet no lowering API builds cleanup pads and native x86_64,
AArch64, RISC-V 32/64 code generation explicitly rejects unwind edges. LLVM can
spell `invoke`, while the LLVM function contract simultaneously declares Simple
functions `nounwind`; this is not a cross-backend language model.

## Missing primitives

- A typed HIR/MIR effect marking calls as `nounwind` or `may_unwind`, preserved
  through direct, indirect, method, facet witness, and foreign calls.
- A canonical MIR throw/resume representation carrying the thrown value.
- Cleanup-pad/landing-pad blocks with defined ordering and exactly-once rules.
- Backend contracts for cleanup and resume on LLVM, C, Cranelift, interpreter,
  and native x86_64/AArch64/RISC-V targets.
- Async state-machine ownership hooks for suspension, cancellation, drop, and
  completion of live descriptor leases.
- Verification proving optimizer CFG rewrites preserve cleanup/unwind edges.

## Current fail-closed boundary

MIR lowering emits fatal `E-AF007` when a possibly live leased facet scope
contains `throw`, `await`, `yield`, or a call to an extern declaration identifiable in
the active HIR module. Indirect/imported foreign calls cannot be classified
because HIR call operands do not retain unwind metadata; they remain unsupported
and must be addressed by the effect primitive above.

## Completion criteria

Remove `E-AF007` restrictions only after all missing primitives exist and focused
tests demonstrate reverse-order, exactly-once release on normal return, throw,
foreign unwind, nested cleanup pads, and async cancellation for every supported
backend.

## D4/D5 evidence audit (2026-08-04)

No isolated backend patch is safe while this defect is open. The remaining
surfaces and their authoritative owners are:

### Indirect facet-call unwind contract

- `src/compiler/50.mir/facet_witness_call.spl:lower_typed_facet_member_call`
  creates the checked descriptor-method call plan.
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:lower_facet_member_call`
  emits the indirect call, but the call instruction has no `nounwind` or
  `may_unwind` fact.
- `src/compiler/50.mir/mir_instruction_support.spl:MirTerminator.CallTerminator`
  can name an unwind target, but normal lowering has no producer.
- `src/compiler/70.backend/backend/native/isel_x86_64.spl`,
  `isel_aarch64.spl`, `isel_riscv32.spl`, and `isel_riscv64.spl` reject unwind
  edges rather than miscompile them.

Acceptance tests must construct a real typed facet indirect call marked with
each supported unwind contract. `nounwind` must preserve the ordinary call and
lexical release. `may_unwind` must either emit a canonical cleanup edge that
releases nested leases once in reverse order on every supported backend, or
produce a typed pre-codegen rejection naming the unsupported backend. A callee
panic/abort test must prove it cannot be mistaken for resumable unwind.

### Prepared-advice backend dispatch

- `src/compiler/50.mir/mir_aop_injection.spl:apply_prepared_advice_result`
  emits `simple.prepared_advice_dispatch.v2` with explicit context.
- `src/compiler/80.driver/prepared_advice_slot_handoff.spl:prepared_advice_driver_bridge`
  validates and rewrites v2 to the source-owned fail-stop dispatcher.
- `src/compiler/70.backend/backend/backend_helpers.spl:backend_prepared_advice_rejection`
  rejects every residual v1/v2 intrinsic.
- `test/01_unit/compiler/mir/prepared_advice_slot_metadata_spec.spl` proves the
  static rewrite, exact unit-return ABI, entry-closure ownership, and residual
  rejection. This is wiring evidence, not executable backend evidence.

Acceptance requires the admitted hosted CPU AOT entry-closure probe to execute
the prepared advice and return the frozen value `73`, retain exact compiler,
fixture, probe-contract, and native-artifact hashes, demonstrate two-context
isolation and held-token unload blocking, and pass
`scripts/check/check-aspect-facet-nfr-evidence.shs`. Every non-admitted backend
must continue returning E-AF010.

### User-facing facet-call sugar

- `src/compiler/20.hir/hir_lowering/expressions.spl` owns recognition and
  preservation of explicit `context.facet<T>(base)` and
  `context.require_facet<T>(base)` as `FacetAcquire`, plus unwrapped method
  provenance as `FacetMemberCall`.
- `test/01_unit/compiler/semantics/typed_facet_source_semantics_spec.spl`
  covers explicit acquisition, wrapper preservation, member provenance, and
  affine escape diagnostics.
- `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
  deliberately defers `base.facet<T>()`: it requires a future lexical context
  and forbids a process-global/current-context fallback.

Acceptance for shorter sugar therefore starts with a selected lexical-context
requirement and syntax. Tests must prove context binding is lexical and nested,
the shortened form lowers to the same explicit `FacetAcquire` context operand,
use outside a bound context is a fatal diagnostic, and no runtime/global
current-context lookup is emitted. Until that requirement exists, the explicit
context spelling is the only supported user-facing contract.

## Portable effect-metadata groundwork

This cannot truthfully be introduced as a facet-only flag. The current ordinary
call is `MirInstKind.Call(destination, function, arguments)` in
`src/compiler/50.mir/mir_instruction_support.spl`; adding metadata changes the
closed instruction shape consumed by MIR JSON/serialization, borrow checking,
every MIR optimizer, the interpreter, and all code generators. Decorating only
`TypedFacetAdapterPlan` would lose the fact as soon as
`lower_typed_facet_member_call` returns a normal `MirInst`, so it would be dead
metadata rather than portable groundwork.

The minimum truthful model is:

1. Define a common `MirCallUnwindContract` with only `NoUnwind` and
   `MayUnwind`. Absence is not permitted; legacy producers must choose
   `NoUnwind` only when their source ABI already guarantees it.
2. Carry the contract on ordinary direct and indirect `MirInstKind.Call` and on
   `MirTerminator.CallTerminator`. Preserve it through MIR cloning,
   serialization, inlining, outlining, SSA, DCE, copy propagation, LICM, and
   auto-vectorization.
3. Add a HIR/source effect owner. `HirFunction.is_extern` alone is insufficient:
   extern declarations need an explicit unwind contract, and function-pointer,
   method, and facet-contract signatures must retain the same fact.
4. Lower `NoUnwind` calls normally. Lower `MayUnwind` only through
   `CallTerminator` after a cleanup target exists; otherwise emit a typed fatal
   diagnostic before backend selection.
5. Keep native backends fail closed until they implement the canonical cleanup
   target. LLVM may emit `invoke` only when the function itself is no longer
   unconditionally declared `nounwind` and the target block contains the
   required landing-pad personality/resume contract.

### Required acceptance specs

- `mir_call_unwind_contract_roundtrip_spec.spl`: direct and indirect calls keep
  the exact contract through MIR JSON and deterministic serialization.
- `mir_call_unwind_optimizer_preservation_spec.spl`: every optimizer named
  above preserves the contract and both successors of `CallTerminator`.
- `facet_member_unwind_contract_spec.spl`: facet method contract metadata
  reaches the emitted indirect call; missing metadata is fatal, never defaulted.
- `facet_cleanup_unwind_edge_spec.spl`: nested leases release once in reverse
  order on an actual unwind successor, while the normal successor releases only
  at its lexical exits.
- `backend_unwind_contract_spec.spl`: unsupported native targets reject
  `MayUnwind` before instruction selection; `NoUnwind` remains an ordinary call.
- `llvm_unwind_contract_spec.spl`: a `MayUnwind` call emits `invoke`, a valid
  landing pad and resume edge, and no contradictory function-level `nounwind`.
- `foreign_unwind_source_contract_spec.spl`: an extern declaration without an
  explicit contract is rejected inside a leased scope; explicit `NoUnwind` is
  admitted and `MayUnwind` requires the cleanup-edge capability.

Until these specs and owners land together, E-AF007 and the native
`CallTerminator` unwind rejections are the authoritative portable behavior.
