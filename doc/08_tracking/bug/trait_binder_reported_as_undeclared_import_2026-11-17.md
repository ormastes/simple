# Trait binder `T` reported as an undeclared import (W-HIR-UNDECL-IMPORT-001)

- **Status:** open
- **Found:** 2026-11-17, while landing PR #9247
- **Severity:** low (staged recovered warning; hard error under `SIMPLE_STRICT_IMPORTS=1`)

## Reproduction

`test/01_unit/compiler/hir/imported_declared_param_metadata_spec.spl`,
example "does not report an uninstantiated trait binder as an undeclared import"
(RED by design).

Provider module `params.traits` imports `Emit` from `params.traitdefs`
(`pub trait Emit<T>: fn emit(value: T)`) and implements `Emit<i64> for Concrete`.
A consumer that only does `use params.traits.{Concrete}` gets:

```
[W-HIR-UNDECL-IMPORT-001] `T` is named in `use params.traitdefs.{...}` but that
module neither declares nor re-exports it (importer params.consumer)
```

## Cause (suspected)

Re-export materialization of the implementor's trait methods
(`module_reexport_materialization.spl`, trait-method branch) resolves the
trait's uninstantiated binder `T` as a nominal type dependency of
`params.traitdefs`, reaching the staged diagnostic at
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:1187`.
A declaration binder is not an importable name and must not be chased.

Pre-existing: the warning is produced by `declared_imported_surface_callable_type`
on the trait method, which predates #9247; #9247 only adds declared-parameter
metadata and explicitly skips trait methods with type parameters.

## Unblock

Skip trait/impl type-parameter names when materializing trait-method signature
dependencies; the RED example above turns green.
