# Class-instance storage: reference semantics in the interpreter

Bugs: `interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17`,
`jit_class_mutation_drop_characterization_2026-07-04`.
Spec: `test/01_unit/compiler/interpreter/class_ref/class_element_reference_spec.spl`.

## Rule
- `class` values are reference types: one heap cell, many handles. Reading a class-typed
  element from a list, array, dict, or field (`xs[i]`, `b.items[0]`, `val c = xs[i]`, a method
  returning such an element) yields the SAME handle. `me` methods and field assignment through
  any handle are visible through all of them.
- `struct` values are value types: every read, bind, and argument pass is a copy.
- Equality, printing, and pattern matching are unchanged; only identity/aliasing differs.

## Current state (verified 2026-11-03)
- Pure-Simple core interpreter (`src/compiler/10.frontend/core/interpreter/`) and the JIT lane
  already honour the rule for the minimal repro (`run` prints 777/42-fixed).
- `bin/simple test` runs the Rust seed tree-walk interpreter. There `Value::ClassInstance`
  (`value.rs`) has zero producers; classes are `Value::Object` (COW struct carrier, `Arc<HashMap>`
  fields) and identity is simulated by path-based write-back. `xs[i].m()` works (in-place path);
  bind-then-mutate loses the write.

## Why no narrow fix
Aliasing needs a shared cell. `Arc::make_mut` on `Object.fields` clones on write, so an
`Expr::Index`-only alias is just another write-back (Option B in the bug, rejected as unsound).

## Required change (seed, then redeploy)
1. Construct `Value::ClassInstance(Arc<ClassInstance>)` (interior-mutable fields) at class
   constructor lowering, keyed by the type's class-vs-struct flag (`Value::aggregate` currently
   ignores `_is_value_type`, `value.rs:~1914`).
2. Add `ClassInstance` arms to the 105 `Value::Object` sites that fall through a wildcard
   (`class_instance_flip_uncovered_sites_2026-09-20.txt`), guarded by the
   `SIMPLE_INTERP_CLASSINSTANCE_TRIPWIRE` tripwire (`b7985a1ef56`).
3. Update `field_assignment_cow_protects_struct_local_alias` to register `Point` as a value type.
4. Remove the path-based write-back special cases once the spec is green; drop `@tag:in-development`.

Verification needs a rebuilt seed (not allowed from this lane) -> verification-pending.

## Status 2026-11-04: default flipped (PR "fix(interp): class reference semantics by default")
- Step 1 done by default: `class_instance_storage_enabled()` is ON unless `SIMPLE_INTERP_CLASS_REF=0`.
- Step 2 partially: arms added where the 256-spec comparison (nogc_async_mut, immut, class_ref_*,
  testing_framework, compiler/interpreter) regressed — method dispatch reuses the Object path
  (arg write-back, trait/blanket impls, callable fields, `__call__`), Some-forwarding field reads,
  structural `==`, `f(obj.field)` write-back, in-place `self.xs.push(..)`, and no receiver rebind
  after a same-class-returning method. One tripwire site still fires with the spec green:
  `patterns::place_method_mutation` (`xs[i].m()`), handled by its fallback path.
- Step 3 unchanged (`Point` test still builds `Value::Object` directly; unaffected by the flip).
- Step 4 (remove path-based write-back special cases) NOT done — follow-up.
- `class_element_reference_spec` and both `class_ref_*_indev_spec` are green and no longer
  `@tag:in-development`.

