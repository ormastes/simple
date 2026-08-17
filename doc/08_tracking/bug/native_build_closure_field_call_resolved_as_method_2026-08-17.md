# Calling a closure-valued FIELD as `self.f(...)` is resolved as a METHOD call on the class

- **Filed:** 2026-08-17
- **Status:** OPEN (root cause in a forbidden path for the filing lane — see Ownership)
- **Reported symptom:** multi-module native build fails on BOTH backends with
  `method owner_collect_fn not found on class ParallelBuilder`
  at `src/compiler/80.driver/driver_build/parallel.spl:248`.

## Summary

A postfix call on a member access, `self.<field>(args)`, is resolved as a
**method call on the receiver's class**, never as an **indirect call through the
value held in the field**. When the field holds a callable (a named `fn` or a
lambda) and no method of that name exists on the class, resolution errors out
instead of invoking the field's value.

This is not specific to `ParallelBuilder` or to `owner_collect_fn`. It is a
defect class: any closure-valued field on any class, called directly.

## Reproduction (verified 2026-08-17)

`bin/simple` here is the **Rust seed** (`bin/release/x86_64-unknown-linux-gnu/simple`,
built 2026-08-16), which prints its own bootstrap-seed warning. All four cases
below were run as `nice -n 19 bin/simple run <file> --timeout 600`.

### RED — named fn in an `any` field, called as `self.cb(a, b)`

```
class Holder:
    name: str
    cb: any

impl Holder:
    me call_it(a: i64, b: i64) -> i64:
        return self.cb(a, b)

fn add_two(a: i64, b: i64) -> i64:
    return a + b

fn main():
    val h = Holder(name: "h", cb: add_two)
    val r = h.call_it(3, 4)
    print("result=" + r.to_string())
```

Verbatim output:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: function 'main' loads a named function as a callable value; the JIT closure ABI has no tag-boxed representation for a bare function pointer (compile_indirect_call would deref the raw code address as a closure struct and call garbage); deferring to interpreter
error: semantic: method `cb` not found on class `Holder`
```

### RED — lambda in an `any` field, called as `self.cb(a, b)`

Same class, `val add = |a: i64, b: i64| a + b` passed as `cb`:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: function 'main' creates a lambda/closure; the JIT closure ABI does not tag-box lambda arguments or results and is incompatible with the runtime's RuntimeClosure layout, so JIT would return wrong values or crash; deferring to interpreter
error: semantic: method `cb` not found on class `Holder`
```

So the defect is independent of whether the callable is a named function or a
lambda.

### GREEN — same lambda, bound to a local first

```
    me call_it(a: i64, b: i64) -> i64:
        val f = self.cb
        return f(a, b)
```

```
[INFO] JIT compilation failed, falling back to interpreter: ... deferring to interpreter
result=7
```

Binding the field value to a local and calling the local is the working
source-level form.

### Field access outside a method is affected identically

`h.cb(3, 4)` at a call site outside the class fails the same way; the receiver
being `self` is not part of the trigger.

## Root cause

`/mnt/data/worktrees/simple-main/src/compiler_rust/compiler/src/interpreter_method/mod.rs:1859`

```rust
bail_unknown_method!(method, class.as_str(), available_methods);
```

This is the terminal `bail` of the `Value::ClassInstance` receiver path in
`evaluate_method_call`. Before reaching it, the path tries, in order:

1. `classes[class].methods`
2. `impl_methods[class]`
3. `TRAIT_IMPLS` for the type
4. `try_method_missing`
5. `try_bare_some_option_method`
6. UFCS fallback — a free function whose name matches the method

and then errors. **There is no step that looks at the instance's FIELDS for a
callable value.**

The contrast that proves this is an oversight rather than a design choice is the
sibling `Value::Object { class, fields }` arm in the *same function*, whose
terminal bail is at `interpreter_method/mod.rs:1338`. That arm *does* consult
the fields first, at `interpreter_method/mod.rs:1297`:

```rust
if let Some(result) = crate::interpreter::interpreter_call::call_value_as_callable(
```

`call_value_as_callable` handles Lambda / Function / BlockClosure /
NativeFunction / Constructor / `__call__`. `Value::Object` receivers therefore
support closure-valued-field calls; `Value::ClassInstance` receivers do not.
A `class ... :` declaration produces a `ClassInstance`, which is why every class
in `src/compiler/**` hits the broken path.

The error text itself is produced by `bail_unknown_method!`, defined at
`/mnt/data/worktrees/simple-main/src/compiler_rust/compiler/src/interpreter/error_macros.rs:58-86`.

### Provenance caveat (important)

The literal string ``method `{}` not found on class `{}` `` does **not** appear
in `simple-main`'s own sources or git history — in this worktree the macro
renders the type-kind word differently. It *is* present in the rodata of the
deployed `bin/simple`, and verbatim in
`/mnt/data/worktrees/simple-v9-qualification-recovery/src/compiler_rust/compiler/src/interpreter_method/mod.rs:1243`.
**The `bin/simple` used for the reproduction above was built from a different
worktree than `simple-main`.** The structural defect (no callable-field fallback
on the `ClassInstance` arm) is present in `simple-main`'s own source at the
line cited above and was read directly there, so the root cause holds for this
tree; only the exact diagnostic wording is worktree-dependent.

## Fix

**Real fix (out of scope for the filing lane):** in the `Value::ClassInstance`
arm of `evaluate_method_call`, before `bail_unknown_method!` at
`interpreter_method/mod.rs:1859`, add the same callable-field fallback the
`Value::Object` arm already has at line 1297 — look up `method` in the
instance's fields and, if the value is callable, dispatch via
`call_value_as_callable`. This makes the two receiver representations agree.

The pure-Simple compiler (`src/compiler/**`) contains no such message and no
such dispatch path; this is purely a Rust-seed interpreter defect.

**Workaround applied in `src/compiler/80.driver/driver_build/parallel.spl`:**
bind `self.owner_collect_fn` to a local before calling it, at both call sites.

## Ownership / scope

The root cause is in `src/compiler_rust/compiler/src/interpreter_method/mod.rs`,
which the filing lane may not edit (lane scope was
`src/compiler/80.driver/**`, `test/**`, `doc/08_tracking/bug/**`; the
method-resolution layers `src/compiler/{10.frontend,20.hir,50.mir,70.backend}`
and the Rust seed were explicitly forbidden). The compiler fix is therefore
**filed, not applied**, and is owned by whoever owns the seed interpreter's
method-dispatch layer.

## Regression guards

- `test/01_unit/compiler/driver/parallel_owner_collect_closure_field_call_spec.spl`
  — the reproducing guard: `parallel.spl` must not contain
  `self.owner_collect_fn(`, and must invoke the hook through a local binding.
- `test/01_unit/compiler/driver/driver_closure_field_call_class_detection_spec.spl`
  — the defect-class guard: sweeps every `.spl` under `src/compiler/80.driver`
  for any `self.<field>(` where `<field>` is a declared `any`-typed field, and
  self-tests its own scanner against a synthetic positive so a vacuous pass is
  impossible.

## Related

`src/lib/common/iterator/reduce.spl:24` already carries a comment recording the
same failure shape (``method `next_fn` not found on class `Iterator` ``), and
`src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl:239` records
another (``method `host_body_mutation_hook` not found on class JsInterpreter``).
Both are instances of this defect class that were previously worked around
in place without the root cause being filed.
