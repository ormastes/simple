# Facet descriptor cleanup lacks portable throw/unwind primitives

Date: 2026-08-04

Status: partial implementation. Typed source/HIR effects, the fail-closed
HIR-to-MIR admission bridge, the explicit MIR call-terminator contract, and its
consumers are implemented and statically reviewed. Cleanup successors and
throw/resume pads, cancellation, and executable verification remain open.

## Problem

A `FacetRef` owns an exact-generation descriptor lease that must be released on
every edge leaving its lexical scope. MIR lowering can insert cleanup on normal
CFG edges, explicit return/error propagation, loop transfer, and aborting panic,
but it cannot represent portable cleanup for language `throw`, async task
cancellation, or a foreign exception crossing a call.

`HirExprKind.Throw` exists, but MIR still has no throw/resume terminator and the
normal lowerer emits no cleanup-pad `MirTerminator.CallTerminator`. The
terminator now carries a required `MirCallUnwindContract` immediately before
its unwind target, and canonical construction validates the only legal pairs:
`NoUnwind` with no edge and `MayUnwind` with an edge. This is MIR groundwork,
not yet a source-to-backend exception model.

The textual LLVM emitter consumes `MayUnwind` as `invoke`; the interpreter
routes a returned call error to the unwind successor. Native x86_64, AArch64,
RISC-V 32/64 and other unsupported targets reject `MayUnwind` explicitly. The
LLVM C-API path also rejects it because its invoke binding is not implemented.
No path may silently lower an inconsistent contract/edge pair.

## Missing primitives

- A canonical lowering owner that creates cleanup successors for typed
  `MayUnwind` calls rather than rejecting them before ordinary call emission.
- A canonical MIR throw/resume representation carrying the thrown value.
- Cleanup-pad/landing-pad blocks with defined ordering and exactly-once rules.
- Backend contracts for cleanup and resume on LLVM, C, Cranelift, interpreter,
  and native x86_64/AArch64/RISC-V targets.
- Async state-machine ownership hooks for suspension, cancellation, drop, and
  completion of live descriptor leases.
- Cross-thread unwind/cancellation ownership and executable parser/import/method
  propagation evidence for the typed HIR effect row.
- Executable verification proving optimizer CFG rewrites and every admitted
  backend preserve cleanup/unwind behavior. Focused static MIR JSON and
  optimizer-preservation specs now exist but have not executed in this lane.

## Current fail-closed boundary

Every declared function now carries exactly one typed unwind effect. Existing
source and extern declarations default to `@no_unwind`; `@may_unwind` is
explicit, and neither extern status nor a string/custom effect infers it.
Callable registration and module-surface import rows preserve the effect for
direct, imported, instance/static/trait, and function-typed indirect calls.

MIR lowering admits an ordinary `MirInstKind.Call` only for `NoUnwind`.
`MayUnwind` fails with `E-MIR-UNWIND001` until a real cleanup successor exists;
missing, duplicate, or conflicting metadata also fails rather than defaulting.
Inside a live facet lease, the same cases preserve the stronger lexical cleanup
diagnostic and fail first with E-AF007. `throw`, `await`, and `yield` remain
E-AF007 while a lease is live.

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
  emits the checked indirect call. The typed callable effect reaches MIR
  admission; unknown effects fail and `MayUnwind` cannot become an ordinary
  indirect call without a cleanup successor.
- `src/compiler/50.mir/mir_instruction_support.spl` owns
  `MirCallUnwindContract`, `validate_mir_call_unwind_contract`, and the canonical
  validated `mir_call_terminator_create`; normal lowering still has no cleanup
  pad producer.
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

Current implementation against the minimum truthful model is:

1. **Implemented from source through admission:** `EffectKind.NoUnwind` and
   `EffectKind.MayUnwind` are typed HIR effects. `@no_unwind` is the compatible
   default, `@may_unwind` is explicit, async remains an independent effect, and
   duplicate/conflicting unwind annotations are fatal. Callable/import/method
   and function-type propagation preserves the exact effect. MIR maps it to
   `MirCallUnwindContract`, admits only `NoUnwind` as an ordinary call, and
   rejects missing/conflicting metadata or `MayUnwind` without a cleanup edge.
2. **Implemented for `CallTerminator`:** common `MirCallUnwindContract` with
   only `NoUnwind` and `MayUnwind`; absence is impossible and the validator
   rejects inconsistent edge pairs. JSON/serialization, borrow analysis, SSA,
   DCE, copy propagation, LICM, outlining, loop/collection analysis,
   interpreter, and backend consumers preserve or reject the explicit value.
   Ordinary `MirInstKind.Call`/`CallIndirect` admission consumes this
   source-derived effect; the instruction itself remains the admitted
   `NoUnwind` form rather than duplicating HIR metadata.
3. **Implemented fail-closed consumption:** textual LLVM emits `call` for
   `NoUnwind` and `invoke` for `MayUnwind`; the interpreter consumes both; the
   LLVM C API and native/unsupported backends reject unsupported `MayUnwind`.
4. **Open:** create cleanup successors and lower source-derived `MayUnwind`
   through `CallTerminator`. The current bridge correctly emits a typed fatal
   diagnostic before backend selection instead of fabricating an unwind edge.
5. **Partially implemented:** native and unsupported backends fail closed.
   Textual LLVM can spell `invoke`, but admission remains blocked until the
   function is no longer contradictorily `nounwind` and the unwind block owns a
   valid landing-pad personality/resume contract. The LLVM C API still needs an
   invoke binding.

### Canonical cleanup landing-pad contract

The missing payload is not the source-language value carried by
`MirTerminator.Throw`. LLVM transfers an implementation unwind record to a
landing pad (on the supported Itanium-style textual path, `{ptr, i32}`), while
the MIR interpreter currently represents all runtime values as scalar `i64`.
Reusing an arbitrary `MirOperand` as both values would silently conflate two
different ABIs.

The minimal portable MIR addition is therefore:

```text
MirTypeKind.ExceptionToken
MirInstKind.LandingPad(dest: LocalId)
MirTerminator.Resume(token: MirOperand)  # operand type must be ExceptionToken
```

The builder surface is `emit_landing_pad() -> LocalId` (allocating an
`ExceptionToken` temp) and the existing `terminate_resume(token)`. The MIR
validation owner is `validate_mir_exception_cfg(body) -> Result<(), text>`.
Facet lowering owns
`emit_facet_unwind_cleanup_successor(first_scope: i64) -> BlockId`; it snapshots
cleanup entries, builds the unwind-only blocks, restores the caller's current
block, and does not mutate `facet_cleanup_scopes`. A `CatchException` instruction
is deliberately excluded: cleanup-only unwinding never decodes or handles the
language payload, and catch semantics require the separate runtime packet ABI.

`ExceptionToken` is compiler-owned and cannot be named, constructed, copied
into user storage, returned, or passed to an ordinary call. `LandingPad` is
valid only as the first non-phi instruction of an unwind-successor block and
defines exactly one `ExceptionToken`. `Resume` is valid only with that token or
a token forwarded through cleanup-only CFG blocks. MIR validation must reject
landing pads reached by normal edges, unwind targets without a landing pad,
tokens consumed by ordinary instructions, and cleanup blocks that return or
fall through instead of resuming.

For one `MayUnwind` call with live facet scopes, lowering must build this CFG:

```text
call_block:
  CallTerminator(..., normal=normal_block, MayUnwind, unwind=cleanup_entry)
cleanup_entry:
  token = LandingPad
  release innermost entries in reverse acquisition order
  release enclosing entries in reverse acquisition order
  Resume(move token)
normal_block:
  continue source evaluation; perform the same lexical cleanup only at its
  ordinary return/break/continue/fallthrough exits
```

Guarded facet entries may split the cleanup path, but the token must dominate
every branch and be resumed exactly once. Emitting the unwind cleanup must not
pop or consume the normal-path cleanup-scope metadata.

Textual LLVM may map `ExceptionToken` to `{ptr, i32}`, emit
`landingpad {ptr, i32} cleanup`, and emit `resume {ptr, i32} %token` only after
the enclosing function declares one canonical runtime-owned personality.
Until that personality and the source-value-to-runtime-exception packet ABI are
specified, textual LLVM must retain E-MIR-UNWIND002 for `Throw`/`Resume` and MIR
lowering must retain E-MIR-UNWIND001 for `MayUnwind` calls without a real cleanup
successor. The interpreter and every non-LLVM backend likewise reject the new
instruction/token until they own a genuine exception representation; no zero,
nil, abort, return, or ordinary branch is a valid substitute.

Ownership is explicit: MIR construction/validation owns landing-pad placement
and token linearity; borrow analysis treats the token as compiler-owned and
non-borrowable; SSA/copy propagation may rename it but not duplicate or erase
it; CFG/DCE/LICM/outlining must preserve the unwind edge, landing pad, cleanup
order, and Resume; backends either implement the entire contract or reject it
before emission.

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
- `mir_landing_pad_contract_spec.spl`: an unwind target begins with exactly one
  `LandingPad(ExceptionToken)` and ends in `Resume` of the same token; normal
  predecessors, user-visible token uses, missing pads, duplicate pads, and
  return/fallthrough cleanup exits are rejected.
- `facet_cleanup_unwind_edge_spec.spl`: in addition to reverse-order release,
  guarded cleanup branches preserve one dominating token and converge on one
  `Resume`; the normal successor retains independent lexical cleanup metadata.
- `mir_exception_token_optimizer_preservation_spec.spl`: borrow, SSA, copy
  propagation, DCE, LICM, and outlining preserve token definition/use and never
  turn an unwind successor into a normal edge.
- `foreign_unwind_source_contract_spec.spl`: an extern declaration without an
  explicit contract is rejected inside a leased scope; explicit `NoUnwind` is
  admitted and `MayUnwind` requires the cleanup-edge capability.

Until the remaining cleanup-successor/pad/resume, async/thread cancellation,
LLVM C-API invoke, executable parser/import/method checks, and NFR evidence
owners land together, E-AF007 and
the native/unsupported `CallTerminator` rejections remain the authoritative
portable behavior.
