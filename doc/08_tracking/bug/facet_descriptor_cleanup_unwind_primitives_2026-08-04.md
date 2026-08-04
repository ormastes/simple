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
