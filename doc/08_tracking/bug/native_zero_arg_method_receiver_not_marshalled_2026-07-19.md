# Native codegen: zero-explicit-arg method call on non-self local receiver never marshals the receiver register

- **ID:** native_zero_arg_method_receiver_not_marshalled_2026-07-19
- **Status:** OPEN (call-site inline workaround landed in engine.spl, fd5e9184c21)
- **Severity:** high (silent wrong-receiver dispatch or nil-receiver panic; latent everywhere)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
`batch.material_supported()` inside `Engine2D._draw_font_batch_plan`
(engine.spl) faulted with cr2=0 ("field access on nil receiver") — or,
worse, silently read the WRONG object's memory — depending on incidental
register pressure.

## Root cause (disassembly-verified two independent ways)
Receiver materialization is folded into explicit-argument marshalling. A
method call with ZERO explicit arguments therefore emits **no
`mov rdi,<receiver>` at all**; the `call` reuses whatever rdi already
holds. Consequences:
- `self`-receiver zero-arg calls accidentally work (rdi == self at entry) —
  which is why this stayed latent.
- Non-self local receivers dispatch on garbage: in the probes-off build rdi
  held a spilled scratch bool (0) → nil panic; in the probes-on build rdi
  held a stale non-null pointer → the call silently treated the enclosing
  `Engine2D` as a `FontRenderBatch` (probe presence MASKED the bug).

Verified not order/CSE-related: hoisting the call first still emitted no
rdi reload; a comparison 3-arg call (`cuda.draw_font_batch(x,y,batch)`)
reloads every argument including the receiver from its spill slot.

## Known latent sibling
`backend_rocm.spl:277` — `batch.material_supported()` same shape, off the
boot path, not fixed. Any zero-arg method call on a non-self local is
suspect until the compiler fix lands.

## Workaround (landed)
Inline the method body at the call site (plain field loads + calls that
carry explicit operands). Maintenance trap: the inlined copy in engine.spl
diverges from the canonical `material_supported` — reconcile when this bug
is fixed.

## Fix direction
Emit receiver marshalling unconditionally in the call lowering (receiver is
argument 0, not a side effect of the explicit-arg loop). Regression test:
zero-arg method call on a non-self local receiver inside a function whose
own self is live, compiled --target x86_64-unknown-none.
