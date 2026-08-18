# native-build's class surface misses a newly added field across modules

**Status:** OPEN (P1 — aborts the native-build worker). Re-triaged 2026-08-17;
not reproduced in isolation, see "Re-triage" below.

## Re-triage 2026-08-17 (seed `bin/release/x86_64-unknown-linux-gnu/simple`, 59537240 bytes, mtime 2026-08-17 12:58:51)

Two things sharpen the diagnosis, both read directly from source:

1. **The message is not emitted by a "semantic pass" at all.** It comes from the
   Rust seed interpreter's runtime field read,
   `src/compiler_rust/compiler/src/interpreter/expr.rs:103-124`
   (`get_field_value`, `Value::Object { fields, class }` arm). It fires when the
   *instance*'s `fields` map lacks the key — i.e. the object was CONSTRUCTED from
   a class definition that did not have the field. So the stale thing is the
   interpreter's global class registry at construction time, not a per-module
   type surface in `src/compiler/**`. `native-build` is implicated only because it
   runs `src/app/cli/native_build_worker.spl` under that same interpreter with the
   whole compiler tree loaded (visible in `ps`), which is where a registry
   collision becomes likely.

2. **The registry is bare-name, last-write-wins** — stated at
   `src/compiler/10.frontend/ast.spl:58-65`, which is the earliest of the three
   instances and was fixed by RENAMING the colliding `Module` to `AstModule`.
   That is a different mechanism from "newly added field", and the two theories
   the "Not verified" list below already flags are still the open question.

   For this instance the collision is not visible in `.spl` sources:
   `grep -rn "^class HirLowering\|^struct HirLowering" src/` returns exactly one
   `.spl` hit (`src/compiler/20.hir/hir_lowering/types.spl:58`); the other two
   hits are fixture strings inside `interpreter_patterns.rs`.

**Debug hook that already exists and should be used next:** `expr.rs:109-116`
dumps the instance's ACTUAL field list under `SIMPLE_DBG_COLLISION=1`. Running
the failing native-build with that set — after temporarily inlining the
accessors in `_Items/module_lowering.spl` back to the direct field read — will
say in one run whether the constructed `HirLowering` is missing only the new
field (stale definition) or has a wholly different field set (collision).

**Not fixed in this pass**, and why: reproducing requires a native-build of the
compiler tree with the workaround reverted. The two builds sharing this host were
already at 11-12 GB RSS each, and this defect's own prior run is recorded as
ballooning to 29.4 GB before being killed. A small two-module fixture (class in
one file, `impl` in a sibling) was written but NOT run to a verdict under
native-build in this pass, so it is not offered as evidence either way; note that
the same shape is used widely across the tree and generally works, so a minimal
fixture is unlikely to be sufficient.

Harder blocker measured the same day: on this host the interpreted native-build
worker **aborts on a single 8 GiB allocation** while loading the compiler graph,
before any semantic work happens (`memory allocation of 8589934592 bytes
failed`, core dumped, misreported by the driver as a 7200s timeout — see
`native_build_static_method_trailing_default_unresolved_2026-08-17.md`). Until
that is fixed, NO native-build-based reproduction of this row is possible here,
including the `SIMPLE_DBG_COLLISION=1` run proposed above.
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
