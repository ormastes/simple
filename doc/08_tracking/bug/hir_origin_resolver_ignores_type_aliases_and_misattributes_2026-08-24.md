# HIR origin resolver ignores `type X = Y` aliases, and blames the wrong file

- **Filed:** 2026-08-24
- **Lane:** Q (slice-B compile sweep)
- **Status:** OPEN — recorded, not fixed
- **Related:** `doc/08_tracking/bug/hir_unresolved_type_owner_missing_import_2026-08-22.md`
  (the record that introduced the two advisories below)

Two symptoms of the same owner-search in
`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
(`[hir-payload-origin-unresolved]` at :486, `[hir-callable-dep-origin-unresolved]`
at :755).

## Symptom 1 — a `type` alias is not counted as a declaration

`src/compiler/30.types/macro_def.spl:14` declares

```
type Symbol = text
```

yet compiling `src/compiler/30.types/macro_checker.spl` emits

```
[hir-callable-dep-origin-unresolved] owner=compiler.types.macro_def dependency=Symbol:
  no declaration, re-export hop, or explicit import of this name in the owner;
  a later `unresolved type: Symbol` will be reported against an importing module instead
```

The declaration is right there in the owner. The walk recognises
`struct`/`enum`/`class`/`fn` declarations and import/re-export hops but not a
type alias, so it reports a false negative.

This matters beyond noise: the advisory's whole job is to name the module that
is really missing an import. When it fires on a module that is NOT missing
anything, it points investigation at the wrong file — and it did, twice, during
this sweep.

## Symptom 2 — errors attributed to a file that never mentions the name

Compiling `src/compiler/35.semantics/__init__.spl` reports

```
[hir-fatal] source_idx=1 path=src/compiler/semantics/auto_defer.spl
  error_idx=0 text=HIR lowering error in src/compiler/semantics/auto_defer.spl:
  unresolved type: FunctionAttr
```

for `FunctionAttr`, `ExportAttr` and `DriverManifestAttr` — but
`grep -c 'FunctionAttr\|ExportAttr\|DriverManifestAttr' src/compiler/35.semantics/auto_defer.spl`
is **0**. The names appear nowhere in the blamed file. (`FunctionAttr` is
defined in `src/compiler/00.common/_Attributes/decl_attrs.spl:667`.) The same
shape appears for `src/compiler/hir/hir.spl` (`ExportAttr`, `LayoutAttr`,
`FunctionAttr`, `DriverManifestAttr`, `VhdlHardwareMetadata`).

A related, smaller span defect: `unresolved name: KeyExtractor at
src/compiler/30.types/const_key_type.spl:45:9` pointed at a `match self:` line,
while the four real `KeyExtractor` references in that file are at lines 214,
227, 236 and 241.

## Why this is worth fixing at the compiler layer

Both symptoms are in diagnostic *quality*, and both cost real investigation
time in this sweep. The correct detection layer is the compiler itself: the
advisory already exists and already knows the owner module — it just needs to
consult type aliases when deciding "declared here?", and to carry the true
source of a payload dependency rather than the importing module's span.

## Not fixed here, deliberately

The owner search is shared, hot, and covered by another lane's record above.
A blind edit could not be verified from this lane: the compiler under test is a
prebuilt stage2, so a source change to `20.hir` has no observable effect until a
bootstrap redeploy. Recorded rather than guessed at.
