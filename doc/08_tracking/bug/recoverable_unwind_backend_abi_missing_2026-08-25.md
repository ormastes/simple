# Recoverable unwind backend ABI is incomplete

Status: partial source implementation / verification pending

## Symptom

Pure-Simple HIR and MIR represent allocation-free exception payload propagation
with `Throw(payload, type_tag)`, `Resume(payload, type_tag)`, and
`CallTerminator` unwind edges. The tree-walk MIR interpreter implements that
contract. Backend support is now target-specific and must remain explicit.

## Remaining root cause

The admitted v1 ABI is a bounded per-thread runtime-frame protocol rather than
host/C++ unwinding metadata. It covers scalar payload/type-tag propagation and
MIR cleanup-pad Resume on the supported lanes below. Remaining gaps are the
llvm-lib C-API control-flow implementation, RV32's unproven two-register i64
return convention, non-ELF object formats, and collision-free structural tags
for composite catch types.

## Required fix

1. Implement llvm-lib runtime-frame control flow, or retain its current stable
   fail-closed diagnostics.
2. Prove an RV32 payload/status return ABI before enabling RV32.
3. Add a separately admitted non-ELF mechanism before enabling Mach-O/Windows.
4. Extend the initial primitive/named runtime type tags to collision-free
   structural identities for composite catch types.
5. Add cross-backend caught, nested-cleanup, rethrow, and uncaught tests.

AST `TryCatch` now lowers through the HIR schema/codec, and the MIR builder
converts calls made in a protected region to `CallTerminator`. Untyped wildcard
and binding catches have CFG lowering. Primitive and named typed catches use an
explicit MIR payload type tag; composite typed catches remain a compile-time
diagnostic pending item 4. Return, break, and continue paths run active finally
blocks inner-to-outer, and catch-body exceptions use a dedicated cleanup pad.

`CallTerminator` keeps its normal typed result destination separate from the
two unwind-only `i64` destinations for exception payload and type tag. Normal
completion writes only the original destination; exceptional completion writes
only the unwind slots before selecting the cleanup edge. This separation is an
ABI invariant for protected calls returning scalar, text, or aggregate values.

Current unsupported paths fail closed with named diagnostics/panics and are
recorded as unsupported by transition coverage.

## Source implementation update (unverified)

The runtime now defines a fixed-capacity thread-local exception-frame ABI:
push, capture/finish, pop, payload/type-tag inspection, throw, and resume. The
textual LLVM emitter and direct x86-64, AArch64, and RV64 selectors contain
POSIX ELF lowering for `Throw`, `Resume`, and unwind-bearing `CallTerminator`.
The C++20 backend rejects Throw, Resume, and unwind-bearing CallTerminator:
generated `std::tuple` locals may be non-trivially destructible, so longjmp
across them would be undefined behavior.
Mach-O rejects before instruction selection; LLVM targets other
than Linux/FreeBSD ELF x86-64, AArch64, and RV64 reject before emitting an
`_setjmp` reference. RV32 rejects because its two-register i64 payload ABI is
not proven. The LLVM C-API (`llvm-lib`) backend explicitly rejects Throw,
Resume, and unwind-bearing CallTerminator; it never substitutes `unreachable`
or silently selects the normal edge.

This narrows, but does not close, the bug. Structural composite type identity
is incomplete, C++ unwind and the LLVM library emitter remain deliberately unsupported, and no
admitted self-hosted run has established caught/nested-cleanup/rethrow/uncaught
semantics on each supported backend. The runtime C frame test passes for nested
resume, payload/type tags, frame balance, and pthread isolation; compiler/backend
execution remains pending. Closure requires those results
plus stable rejection evidence for every deliberately unsupported backend.

## Support-matrix clarification (unverified)

The intended native support set is exactly POSIX ELF x86-64, AArch64, and RV64.
The C backend, LLVM library emitter, Mach-O, and RV32 are not silent fallback
lanes: their current behavior is deliberate fail-closed rejection until a
target-specific ABI is designed and proven. Textual LLVM on the supported set
and the three direct selectors still require executable caught/cleanup/rethrow/
uncaught evidence before this record can be narrowed or closed.
