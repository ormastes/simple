<!-- codex-architecture -->
# MIR landing-pad backend contract (2026-08-04)

## Status

Blocked by missing canonical exception representation. `Throw` and `Resume`
must continue to fail with `E-MIR-UNWIND002`; emitting plausible LLVM or native
control flow would be invalid.

## Evidence

### Textual LLVM

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` can spell an
`invoke`, but its unwind destination is an ordinary MIR block. The builder in
`src/compiler/70.backend/backend/llvm_ir_builder.spl` declares functions
`nounwind` and has no personality declaration, landing-pad builder, catch or
cleanup clauses, or resume builder.

LLVM `resume` cannot consume a Simple language value. It must consume the exact
exception aggregate produced by a landing pad under a compatible personality.
The current `MirOperand` gives no proof that a `Resume` operand has that origin
or representation. Therefore textual LLVM cannot validly lower either new
terminator today.

### LLVM C API

`src/compiler/70.backend/backend/llvm_lib_translate.spl` has bindings for calls,
branches, and unreachable, but none for setting a personality, building a
landing pad, adding clauses, or building resume. It also has no exception
aggregate type. The current explicit rejection is authoritative.

### MIR interpreter

`src/compiler/95.interp/mir_interpreter.spl` represents failures as
`InterpError`. A `MayUnwind` call can select its unwind successor, but the
callee error is discarded when that jump occurs. There is no pending-exception
slot, landing-pad bind operation, handler stack, or distinction between a
language thrown value and a backend unwind token. Consequently `Throw` cannot
route a value and `Resume` cannot continue the original failure.

### Native backends

The x86-64, AArch64, RV32, and RV64 selectors have no personality routine,
unwind-table emission, exception object ABI, landing-pad entry convention, or
resume primitive. Their `E-MIR-UNWIND002` rejection points are correct.

## Minimal canonical contract

Backend activation requires all of the following to land together:

1. Add an opaque MIR exception payload type, distinct from ordinary language
   values. A `Resume` operand must have this type.
2. Add a landing-pad entry operation that binds the current opaque payload to a
   local. The verifier must require it at every `MayUnwind` successor before
   that block reads or resumes the payload.
3. Define `Throw(value)` as creation/raising of a runtime exception object from
   a language value. Define `Resume(payload)` as propagation of the unchanged
   opaque payload. These operations are not interchangeable.
4. Attach a personality/exception ABI to each function containing `invoke`, a
   landing pad, `Throw`, or `Resume`. The ABI must define exception allocation,
   ownership, cleanup, selector meaning, and cross-module compatibility.
5. Validate CFG provenance: ordinary branches cannot enter a landing pad;
   unwind edges must enter one; a resumed payload must originate from the
   active landing pad and must not escape as a normal value.
6. Give the interpreter a pending exception record and landing-pad bind step.
   Nested calls must preserve the original record until handled or resumed.
7. Add backend capability gating so unsupported targets reject before partial
   emission. No backend may translate `Throw` to abort, normal return, or an
   ordinary branch.

Suggested shared names are `MirTypeKind.ExceptionPayload`,
`MirInstKind.LandingPad(dest)`, and function metadata
`MirExceptionAbi(personality, representation_version)`. Names remain proposed;
the semantic distinctions and verifier rules are required.

## Activation sequence

1. Land MIR types, verifier rules, serialization, optimizer preservation, and
   interpreter pending-exception semantics.
2. Select and document one runtime/personality ABI.
3. Add textual LLVM personality, landing-pad aggregate, and resume emission;
   remove `nounwind` only where the verified function requires unwinding.
4. Add equivalent LLVM C API bindings and parity tests.
5. Keep native and portable backends rejected until they independently satisfy
   the same contract.

## Verification gates

- LLVM verifier accepts nested throw, cleanup, and resume fixtures.
- A landing pad observes the original thrown value.
- Cleanup followed by resume reaches the caller's unwind successor.
- Cross-module callers agree on personality and representation version.
- Optimizers preserve landing-pad placement and payload provenance.
- Unsupported backends return `E-MIR-UNWIND002` before emitting output.

## Ownership

- Sidecar lanes: N/A (bounded static feasibility audit).
- Merge owner: root feature coordinator.
- Final reviewer: normal/highest-capability verifier after runtime ABI selection.
