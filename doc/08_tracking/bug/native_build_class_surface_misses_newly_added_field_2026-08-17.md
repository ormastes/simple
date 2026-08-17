# native-build's class surface misses a newly added field across modules

**Status:** OPEN (P1 — aborts the native-build worker)
**Filed:** 2026-08-17
**Component:** native-build semantic pass (pure-Simple), cross-module class fields
**Class:** engine divergence — the seed interpreter resolves it, native-build aborts

## Symptom

Reading a **newly added** field of a class from a sibling module — an
`impl HirLowering:` in a *different* file from the one that declares the class —
aborts the whole native-build worker:

```
class `HirLowering` has no field named `imported_type_methods_in_progress`
```

The field **is** declared, in `src/compiler/20.hir/hir_lowering/types.spl`, and
the Rust seed interpreter resolves it without complaint. Only native-build's
semantic pass rejects it.

## The revealing detail

Every *other* cross-module field access on this same class works. The difference
is age: those fields predate whatever class-surface snapshot native-build builds,
so only a **newly added** field trips it. That points at a stale or
incompletely-populated class surface rather than at cross-module access being
unsupported in general.

Same shape is already recorded at `src/compiler/10.frontend/ast.spl:65` and
`_Items/module_lowering.spl:2029` — this is at least the third instance, so it is
a recurring surface-construction defect, not a one-off.

## Current workaround, and why it is shaped this way

Accessors (`imported_type_methods_in_progress_has` / `_push` / `_pop`) live in
`types.spl`, the module that DECLARES the class, and
`_Items/module_lowering.spl` touches the field only through them. The site
carries a `Do NOT inline these back` comment so the workaround is not "tidied"
away by a later reader — the direct form is what aborts.

## Why it matters beyond this one field

The failure is **fatal to the worker**, not a warning, so it takes down an entire
native build. And it is silent about its real cause: the message says the field
does not exist, when the field plainly does. Anyone hitting it will go looking
for a typo or a missing declaration rather than a stale class surface.

## Fix direction

Find where native-build's semantic pass builds its class surface and ensure a
field added to a class declaration is visible to `impl` blocks in sibling modules
in the same compilation. Until then, any newly added field on a class whose
`impl` blocks are split across modules must be reached through accessors declared
beside the class.

## Not verified

- Whether `var`/`val` fields differ from method visibility in the same way.
- Whether the surface is stale (built before the field was added) or simply
  scoped per-module — the two have different fixes.
- Whether the JIT lane shares the defect; only native-build and the seed
  interpreter were compared.

Found while working the compiler `.spl` slice; the accessor workaround is in the
same change that filed this row.
