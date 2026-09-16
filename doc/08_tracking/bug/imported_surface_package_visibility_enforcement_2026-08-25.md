# Imported surface package visibility is not enforced

## Evidence

`ModuleSurfaceCallable.visibility` retains the declaration visibility and both
the requester and owner surfaces retain canonical `package_name`. However,
`HirLowering.register_imported_symbol_inner` defines imported free functions
with `Visibility.Public` unconditionally in
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`.
The same unconditional widening exists for imported constants, composites,
traits, aliases, and re-exported methods.

The crypto siblings `std.common.crypto.sha512` and
`std.common.crypto.types` both normalize to package `std.common.crypto`, so
their `pub(package)` dependency is valid. A module outside that package is not
currently rejected reliably by the retained-surface import path.

## Required fix

Before defining an imported symbol, compare requester and declaring surface
packages when retained visibility is `Visibility.Package`; reject an
out-of-package route with the canonical visibility diagnostic. Preserve the
retained declaration visibility instead of rewriting it to Public. Apply the
same rule to direct imports and re-export materialization for every declaration
kind, with same-package, outside-package, alias, and facade tests.

This needs shared requester-package plumbing across several registration paths;
it must not be approximated only for crypto callables.
