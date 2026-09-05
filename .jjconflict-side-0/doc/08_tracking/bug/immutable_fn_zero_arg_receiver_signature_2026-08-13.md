# Immutable zero-argument instance `fn` loses its callee receiver signature

- **ID:** immutable_fn_zero_arg_receiver_signature_2026-08-13
- **Status:** parser/HIR/MIR source repair in progress; self-hosted native execution pending
- **Severity:** high — a legal immutable instance method can be emitted with
  an ABI signature that has no receiver
- **Related:** `native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25.md`
  and `fv2_gate_collector_selfhost_compile_segv_2026_08_12.md`

## Minimal form

```simple
class Positive:
    value: i64
    fn has_value() -> bool:
        self.value > 0
```

`fn` means an immutable instance method when it appears in a class/impl body.
It is not equivalent to `static fn`.  The generated callable therefore has
one ABI parameter, `self`, despite having zero explicit source arguments.

## Root cause

The Rust parser treated a plain `fn` method with no explicit `self` as an
implicit static/factory method. That erased the receiver before HIR/MIR and
made the import ABI arity zero. Static factories must be written `static fn`;
plain `fn` is an immutable instance method even when it has zero source
parameters. The pure-Simple HIR owner context remains authoritative and now
preserves the method bit defensively for staged/self-hosted lowering.

MIR rejects any non-static method that reaches it without an ABI receiver, and
native import discovery records the parser's canonical parameter list without
repeating a receiver-synthesis heuristic. Native static-call codegen rejects
an impossible declared arity before argument adaptation can hide a mismatch.

This is a signature/lowering defect, not a mutability defect. Changing the
method to `me` is explicitly not an acceptable fix: it changes the language
semantics and hides the same ABI failure for every other immutable instance
method.

## Repair

Rust parser receiver synthesis is now canonical: every non-static plain `fn`
or `me` method has an ABI-visible leading `self`; only explicit `static fn` is
receiver-less. HIR derives an effective instance-method bit from its enclosing
owner context whenever the declaration is not static, consistently using it
for symbol identity, receiver synthesis, and `HirFunction.is_method`. MIR
rejects malformed receiver signatures, while native import/codegen checks keep
the published ABI arity fail-closed. No `me` workaround is involved.

The focused HIR regression is
`test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl`, which
asserts that `fn has_value() -> bool` has exactly one `self` parameter and is
not static; the Rust parser regression covers the adjacent explicit-static
case. A fresh admitted pure-Simple compiler must run that test and the
native `check-native-immutable-fn-receiver.shs` receipt before this bug can be
closed.
