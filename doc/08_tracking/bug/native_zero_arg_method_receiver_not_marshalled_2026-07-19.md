# Native codegen: investigate target-only zero-arg method receiver corruption

- **ID:** native_zero_arg_method_receiver_not_marshalled_2026-07-19
- **Status:** FIX CANDIDATE (refreshed hosted AArch64 disassembly verified; wider native matrix pending)
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

## Hosted AArch64 reproduction (2026-07-25)

The self-hosted Stage 3 Cranelift compiler reproduced the defect in the
production HTML/Draw IR renderer on macOS arm64. In
`_engine2d_draw_ir_adv_composition_with_images`, adjacent calls to
`eng.font_execution_target()` and
`eng.vulkan_font_performance_evidence()` were emitted without reloading `eng`
into `x0`. The first getter returned the empty-text value `0`; LLDB then
stopped at the second getter with `x0=0`. Caller disassembly shows the two
indirect branches at offsets `+632` and `+680` with no receiver move between
them. The second getter trapped at its nil-receiver guard or loaded a
text-shaped invalid address, depending on backend/register state.

The same current binary failed with a five-rectangle HTML fixture on
`cpu_simd` and with the production Aetheric HTML on `software`, ruling out the
SIMD implementation, gradients, and the WM runtime-provider link as the root
cause. A diagnostic direct-field substitution passed the former crash point,
but it is intentionally not retained: Draw IR continues to call the canonical
Engine2D getters, and the fix belongs at receiver argument construction.

The source helper was semantically receiver-first, but it initialized the
generic operand array with a one-element literal. In the affected self-hosted
compiler that literal can become an empty runtime array, so the MIR `Call`
reaches backend lowering with zero arguments even though the source helper
looks correct. Both receiver-first helpers now start with `[]` and explicitly
push `mir_operand_copy(receiver_local)`; the unresolved cross-module recovery
path does the same for `unresolved_receiver_local`.

A refreshed hosted AArch64 Stage 3 compiler built from this change emits
`mov x0, x22` immediately before both focused getter calls. The same receiver
is preserved across the optional field write and the text-returning first
getter, proving that the explicit push changes the emitted call ABI. The first
version of the fixture still exited 132 only because its final
`evidence.?.marker` assertion exposed a separate ExistsCheck defect:
`rt_is_some(evidence)` returned an `i1`, and native code then used that boolean
as the struct field receiver. That defect is tracked separately; the receiver
regression now checks the returned optional handle for non-nil, which is enough
to prove the second getter received the correct object. Promotion from FIX
CANDIDATE still requires the focused fixture on hosted arm64 plus x86/ARM QEMU.

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

## Triage 2026-08-17 (lane m7c_lib_async) — UNVERIFIED

The symbol named in this doc, `_draw_font_b`, does not exist in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl`; the family present is
`_draw_font_batch` (:1453), `_draw_font_batch_plan` (:1544),
`_draw_font_batch_staged` (:1520), `_draw_font_batch_cpu_suffix` (:1456).
The defect is a NATIVE-codegen receiver-marshalling fault, so it cannot be
exercised from a spec body (which runs interpreted) and needs a native
subprocess plus GPU backends absent on this host. Recorded UNVERIFIED — neither
reproduced nor closed.
