# Recoverable unwind backend ABI is incomplete

Status: partial source implementation / verification pending — **BLOCKED 2026-11-11 (lane compiler6): closure needs the self-hosted native lane on POSIX ELF; seed-lane verification recorded in the 2026-11-11 addendum. OPEN kept.**

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

## Verification addendum 2026-11-11 — lane compiler6 (BLOCKED, OPEN kept)

Lane compiler6 verified what the seed lane can reach, on the tracked fresh
seed (`bin/simple.exe`, build 46fe8f6b6def, seed-smoke):

* `test/01_unit/compiler/interp/mir_recoverable_unwind_spec.spl` —
  re-run GREEN: `7 executed, 7 passed, 0 failed`. Covers the tree-walk MIR
  interpreter side of the contract: f64/text/aggregate normal results stay
  separate from the unwind payload storage, a thrown payload reaches the
  unwind-edge destination, `Resume` preserves the payload across a frame,
  the explicit type tag survives on the unwind edge, and an uncaught
  exception is not misclassified as a normal return.
* `test/01_unit/compiler/backend/recoverable_unwind_typed_dest_source_spec.spl`
  — re-run GREEN: `2 executed, 2 passed, 0 failed`. Pins the source contract
  in the textual LLVM emitter (`_MirToLlvm/core_codegen.spl`, Throw/Resume at
  :2093/:2109) and in all three supported direct selectors
  (`isel_x86_64.spl:1496`, `isel_aarch64.spl:901`, `isel_riscv64.spl:917`):
  each consumes the dedicated `unwind_payload_dest, unwind_type_tag_dest`
  pair and `rt_exception_caught_type_tag`.
* Fail-closed rejection is present in source for one deliberately unsupported
  lane: `native/native_macho.spl:27` rejects Throw/Resume before emission.

What this lane could NOT verify (host-bound, not defect-bound): items 1, 2,
3, 4 remain deliberate deferrals, and item 5's "admitted self-hosted run ...
on each supported backend" requires (a) a deployed self-hosted compiler —
surface `try/catch` is pure-frontend only; the Rust seed parser has no
TryCatch production, so no seed-parsed source program can reach these
backends — and (b) a POSIX ELF host for x86-64/AArch64/RV64 native runs.
This host has neither (tracked seed is cranelift-only, Windows COFF).

Exact grant to unblock: deploy the self-hosted stage2/3 binary on a
Linux/x86_64 host, then run a try/catch fixture matrix
(caught / nested-cleanup / rethrow / uncaught) through
`bin/simple native-build` for x86_64, AArch64 (qemu), and RV64 (qemu)
ELF lanes, plus the runtime C frame test, and pin the llvm-lib / C++20 /
Mach-O / RV32 rejection diagnostics in a seed-runnable spec.
