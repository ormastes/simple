# HIR: a package sibling's same-named type shadows the module's own declaration

Status: fixed on `work/rel-hir-samename-20261010` (pure-Simple HIR; not yet
verified on a stage2 native build).

## Symptom

Two directory siblings both declare a type with the same name:

```
lib/dep.spl:    pub enum Status: Ready, Done
                pub struct Job: status: Status
lib/other.spl:  pub enum Status: Mine, Other   (plus Pad, Kind)
```

After HIR lowering, `lib.dep`'s own symbol table had **no** `lib.dep` `Status`.
`Job.status` was bound to `Status@lib.other`, and `lib.dep`'s `enums` held
only `Status@lib.other`. The bug was symmetric: `lib.other`'s `Status` was
replaced by `lib.dep`'s. Measured with the seed interpreter running the
pure-Simple HIR (spec below, before the fix):

```
dep Job.status -> Status@lib.other
dep enums      -> Status@lib.other;
other enums    -> Status@lib.dep;Kind@lib.other;Pad@lib.other;
```

Downstream it showed up as MIR lowering binding struct fields to the wrong
enum (found while fixing the stage2 enum-`==` failure in 25fbd168fa3 /
50abed005d5). The real tree has 2+ modules declaring the same short type names
in one directory, so stage2 builds can hit this silently. The result is a
wrong type identity, not a diagnostic.

## Root cause

1. `resolve_package_sibling_symbols`
   (`src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl`)
   implements directory-package semantics. It prebinds every sibling's
   public types into the module's SymbolTable (via
   `register_imported_symbol`, which `define`s an `Enum` symbol owned by the
   sibling). This happens BEFORE the module's own declare pass.
2. `declare_module_symbols`
   (`_Items/module_declarations_bootstrap.spl`) declares the module's own
   types with `SymbolTable.define`. `define` is **first-write-wins** for type
   symbols (`hir_types.spl` `define_with_binding`), so it returned the
   sibling's symbol, and the module's own declaration was never allocated.
   (The comment at the enum site already noted "define retains an existing
   lexical binding on a name collision".)

Classes take the canonical `(owner, name)` path and did get their own symbol,
but the unqualified scope binding still pointed at the sibling's class.

## Fix

`HirLowering.define_own_module_type` (module_declarations_bootstrap.spl) is
used for the module's own class/struct/enum/bitfield/trait declarations. It
works in two steps:
- If `define` hands back a declaration owned by another module, it drops that
  unqualified binding (`SymbolTable.unbind_local_type`) and defines again,
  which allocates the module's own symbol.
- If the module's own declaration was allocated but the unqualified spelling
  still names a foreign type (the class path), it rebinds the spelling
  (`SymbolTable.rebind_local_type`).

The sibling stays reachable through its qualified binding. With no
`module_filename`, the old behaviour is unchanged.

## Regression

`test/01_unit/compiler/20.hir/package_sibling_same_name_enum_spec.spl`. It
uses three modules with two `Status` enums. Before the fix 0/3 passed; after,
3/3 pass (seed `C:/dev/simple-rel-seed-elif/src/compiler_rust/target_wt/debug/simple.exe`).

## Explicit imports of the same name (review follow-up)

The declare pass runs after Pass 0, so `define_own_module_type` also shadows
an EXPLICIT `use x.{Status}` when the module declares its own `Status`. The
seed was checked (`use app.zzprobe.provider.{Status}` plus a local
`enum Status: Mine, Other`). It accepts the program silently and the local
declaration wins outright: `Status.Mine` runs, and `Status.Ready` fails with
`unknown variant or method 'Ready' on enum Status`. Making this a compile
error would diverge from the seed, so the HIR matches the seed instead. A
materialized import of the shadowed name is no longer lowered
(`lower_module_enum_definitions`), and it no longer re-registers its unit
patterns over the module's own (`module_build.spl`). Before that change, the
module's HIR held `Status@lib.other` and lost its own enum (spec case
"explicit import of a name the module also declares": 5/6 before, 6/6 after).
