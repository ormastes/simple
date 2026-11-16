# Phase-2: method call on an indexed module-global receiver (`g[0].set(i, v)`)

Status: OPEN (analysis only; not a small local fix). Not fixed in this change.
No existing doc found for `phase2_mir_unresolved_field_receiver_2026-11-15` in doc/08_tracking/bug.

## Symptom (frozen Phase-2 build, `src/compiler/10.frontend/core/_AstExpr/nodes.spl:395,612-632`)
`var expr_attr_extra_stores: [AttributeStoreV1<i64>]`:
- `expr_attr_extra_stores[0].set(i, v)` emitted `call i64 @rt_array_get(...)` then
  `call i64 @...AttributeStoreV1.set(ptr %l71, ...)` with `%l71` of type i64 (no inttoptr),
  and the callee declared varargs `declare i64 @...set(...)`.
- `match expr_attr_extra_stores[0].get(idx): case Ok(..)` failed in MIR lowering:
  "bare variant 'Ok' is ambiguous ... unknown receiver.get()".

## Locations (current release/1.0.0 source)
- `receiver_declared_type` (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3006`)
  has arms for Var, NamedVar, Field, Unwrap but NO `Index` arm; the "unknown receiver" text
  comes from `enum_match_ambiguity_subject_hint` (`:3151`). `declared_container_read_type`
  (`:3067`) already computes the element type of `xs[i]` over a declared `[T]`/Dict, but is not
  consulted for an Index receiver. Candidate minimal fix: add
  `case HirExprKind.Index(_, _): return self.declared_container_read_type(receiver)` to
  `receiver_declared_type` (recursion safe: that function calls receiver_declared_type only on the index base).
- The `ptr` operand typed on an i64 value and the varargs declaration are a separate LLVM-emitter
  call-operand coercion/declaration issue that follows once the receiver type is unknown (the method
  is not resolved to a typed callee, so the declaration falls back to `(...)`). Needs reproduction
  with a MIR-level fixture before changing the emitter.

Not verified: whether the Index arm alone removes both symptoms; no spec was written because
reproducing requires a full HIR fixture and a seed able to run it.
