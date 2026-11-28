# JIT segfault: block-scoped `use` of two lazily loaded same-named classes
## Registered 2026-11-27 by p3sweep4 lane (residual of interpreter_lazy_same_name_class_entry_ambiguous_type_2026_11_27)

**Status:** OPEN
**Severity:** P3
**Lane observed:** Windows x86_64, tree-built seed

## Symptom

With two same-named classes imported block-scoped (a `use` inside a function
body or `it` block), the interpreter lane now resolves correctly (fixed by
the parent bug's `module_cache.rs` change), but the JIT lane **segfaults**
(exit 139) on the same shape:

```simple
fn main():
    use test.fixtures.same_name_class.pa.{Thing}
    use test.fixtures.same_name_class.pb.{Thing as Legacy}
    val a = Thing.create()
    ...
```

The module-scope `use` form works on both lanes (flattened import-binding
markers give the HIR lane owner bindings).

## Root cause direction

HIR lowering of lazily loaded colliding classes: the block-use arms bind the
constructor into the local env + flat `MODULE_GLOBALS`
(`interpreter/node_exec.rs:1154`) but record no owner binding, so the HIR
lane sees two colliding bare-name classes with no disambiguation and crashes
in lowering. The fix direction (from the parent lane): the block-use arms
should record `record_owner_binding` (as `evaluation_helpers.rs:72` does for
module-scope uses) so the HIR lane sees owner bindings; the crash site
itself then needs a `hir/lower` investigation to confirm fail-closed behavior
instead of the SEGV.

## Acceptance

The block-use shape compiles and runs on the JIT lane (matching the
interpreter lane's owner-aware resolution), pinned by a regression spec;
the interpreter lane's `same_name_class_block_scoped_import_spec.spl` covers
the interpreter half today.
