# Group import of a self-named module shadows the class, killing static dispatch (2026-08-24)

Status: **FIXED** (seed interpreter, `interpreter_method/mod.rs`).

## 1. Symptom

`use a.b.Foo.{Foo}` — where the module FILE and the class inside it share a
name — bound the module's *namespace dict* to `Foo`, not the class. Every
static call through that name then died:

```
semantic: method `from_lexer_output` not found on type `dict`
  (receiver value: {TokenStreamView: <constructor:TokenStreamView>,
                    TokenStreamView__from_lexer_output: <fn:TokenStreamView__from_lexer_output>, ...})
```

The receiver debug text is the proof: the constructor AND the mangled static
are both sitting in the dict the call was made on — nothing was missing, the
dispatcher just had no arm that looked at them.

Observed on the 2026-08-24 phase-1 sweep across `MirProgram.empty`,
`MirOptView.empty`, `ObjectFileView.from_codegen`/`.failed`,
`LoadedModuleView.from_source`/`.empty`, `TokenStreamView.from_lexer_output`,
`Widget.kind`, `Gadget.kind`, `Severity.ffi_in_verified_error` — one cause, 4
specs, 36 failing examples.

## 2. Fix

`src/compiler_rust/compiler/src/interpreter_method/mod.rs`, in the existing
Dict-receiver arm, after the direct `module_dict.get(method)` lookup: scan the
dict for `Value::Constructor { class_name }` entries whose mangled static
`{class_name}__{method}` is also a function in the same dict, and dispatch it
through `exec_function_with_captured_env`. Two or more matches are left
ambiguous and fall through to the existing error.

Deliberately narrow: it only fires on a path that previously always errored, so
it cannot change the meaning of any call that already resolved. Import binding
order was **not** touched — that is the broader design question and carries
real regression risk.

## 3. Reproduce tests

Already in the tree and failing before this change; passing after:

- `test/01_unit/compiler/module_resolver/group_import_self_named_module_spec.spl`
- `test/01_unit/compiler/module_resolver/group_import_shadowing_generalization_spec.spl`

Defect-class neighbours covered by the same run:

- `test/01_unit/compiler/mdsoc/transform_adapters_spec.spl`
  (67 total, 35 passed / 32 failed → 67 passed / 0 failed)
- `test/01_unit/compiler/verification/verification_diagnostics_spec.spl`

## 4. Limit

Measured on the **Rust seed** binary. Per `.claude/rules/bootstrap.md` these
numbers must be re-measured on a self-hosted `bin/simple` before they can be
called the product's behaviour.
