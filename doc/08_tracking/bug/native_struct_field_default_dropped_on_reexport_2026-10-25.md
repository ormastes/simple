# Seed native-build drops field `= default` for types reached via glob re-export

- Date: 2026-10-25
- Status: FIXED for scope-free defaults (literals, `nil`, `[]`, `{}`); open for
  non-literal defaults (see "Remaining gap")
- Root cause of: `hir_cache_selfcheck_nil_in_non_optional_scalar_2026-10-25.md`
  fix 4 (`HirSymbol.generic_param_count: i64 = 0` encoded as `N`), and the
  general form of its fix 3.

## Symptom

Stage 2 is compiled by the Rust seed (`SIMPLE_NATIVE_BUILD_RUST=1
native-build`). In that binary an omitted constructor field holds the nil tag
`3` instead of its declared default. The pure-Simple MIR lowering
(`switch_operators_calls.spl`, omitted-field fill) is NOT affected: stage2
compiling `struct P: a: i64; b: i64 = 7` + `P(a: 1)` emits `movq $7` for every
shape tried (same module, cross module, class method, flat closure mode).

Repro (seed `build/c/.../bootstrap/simple.exe`, Windows gnullvm):

```
# defs.spl: struct Sym: ... gpc: i64 = 12345
# reexp.spl: pub use defs.*
# main.spl:  use reexp.*  ;  print(Sym(...omit gpc...).gpc)
```

prints `3`. With `use defs.{Sym}` it prints `12345`.

## Root cause

`Lowerer::lower_struct_init_fields` (`src/compiler_rust/compiler/src/hir/lower/expr/collections.rs`)
fills an omitted slot from `struct_field_defaults`, which only
`register_struct` / `register_class` populate. A type reached through a glob
re-export (`use compiler.hir.hir.*` -> `pub use hir_types.*`) is never
registered in the constructing module; its layout comes from the
whole-program `global_struct_defs` map, which carried field names/types but
no defaults. Every omitted slot therefore got `HirExprKind::Nil`.

## Fix

The import-map pass (`native_project/imports.rs`) now records each type's
declared defaults under the same canonical `module_prefix__Type` owner as
`struct_defs`; the lowerer receives them (`set_global_struct_field_defaults`)
and uses them when the type has no local entry, only if that owner's layout
equals the constructor's declared field list (so a same-named type cannot
lend defaults). Only scope-free defaults are borrowed, because the expression
is lowered in the constructing module. Each construction lowers the default
afresh, so `= []` is not shared.

Specs: `test/01_unit/compiler/codegen/reexport_field_default_native_spec.spl`
(probe `reexport_field_default_probe/`), Rust unit test
`test_lower_omitted_field_uses_global_declared_default`.

## Remaining gap

A non-literal default (`= Inner()`, `= SOME_CONST`, `= Kind.A`) on a type
reached only through a glob re-export still gets nil: it may name something
not visible in the constructing module (borrowing `= Inner()` failed codegen
with "cross-module call 'Inner' resolved to data/type export"). Fixing it
needs the default lowered in the declaring module's scope. Until then such
fields must be passed explicitly at those construction sites.
