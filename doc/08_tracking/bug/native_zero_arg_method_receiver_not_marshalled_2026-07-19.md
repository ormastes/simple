# Native codegen: investigate target-only zero-arg method receiver corruption

- **ID:** native_zero_arg_method_receiver_not_marshalled_2026-07-19
- **Status:** OPEN (the current source-level receiver-omission diagnosis is refuted; reproduce below the MIR boundary)
- **Severity:** high on the affected kernel path; no evidence of a universal method-call defect
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
`batch.material_supported()` inside `Engine2D._draw_font_batch_plan`
(engine.spl) faulted with cr2=0 ("field access on nil receiver") — or,
worse, silently read the WRONG object's memory — depending on incidental
register pressure.

## Original target observation
The affected kernel disassembly appeared to omit `mov rdi,<receiver>` for a
method call with zero explicit arguments. Consequences of that generated code
would be:
- `self`-receiver zero-arg calls accidentally work (rdi == self at entry) —
  which is why this stayed latent.
- Non-self local receivers dispatch on garbage: in the probes-off build rdi
  held a spilled scratch bool (0) → nil panic; in the probes-on build rdi
  held a stale non-null pointer → the call silently treated the enclosing
  `Engine2D` as a `FontRenderBatch` (probe presence MASKED the bug).

Verified not order/CSE-related: hoisting the call first still emitted no
rdi reload; a comparison 3-arg call (`cuda.draw_font_batch(x,y,batch)`)
reloads every argument including the receiver from its spill slot.

## Current-source correction
The universal source-level explanation does not match the current compiler.
`lower_receiver_and_args` initializes the MIR argument list with the receiver
before visiting explicit arguments. Resolved instance, trait, UFCS, and
unresolved instance calls all use a receiver-first helper. Cranelift direct and
indirect call lowering then forwards every MIR argument, and the SFFI provider
consumes all staged arguments. Static methods are the intentional exception.

The existing target disassembly remains useful evidence of a downstream or
artifact-specific failure, but it does not justify changing common method-call
lowering. Capture the MIR call argument count and Cranelift IR from the exact
failing artifact before assigning a code owner.

## Known latent sibling
`backend_rocm.spl:277` — `batch.material_supported()` has the same source shape
and remains worth exercising on its real target. It is not evidence by itself
that hosted or common call lowering is defective.

## Workaround (landed)
Inline the method body at the call site (plain field loads + calls that
carry explicit operands). Maintenance trap: the inlined copy in engine.spl
diverges from the canonical `material_supported` — reconcile when this bug
is fixed.

## Next evidence and regression
The cross-module native fixture now calls a zero-argument method on a local
receiver whose value is 37 while the enclosing `self` remains live with marker
99. The existing matrix executes that fixture with LLVM and Cranelift on hosted
systems and on AArch64/RV64 QEMU; ARM32/RV32 and Windows ARM keep compile-only
receipts. A stale receiver therefore fails deterministically rather than
silently passing.

For the kernel-only symptom, record that this exact call has one MIR argument,
then capture Cranelift IR and disassembly. Fix the first layer where the
receiver disappears; do not add another receiver in MIR while it is already
present.
