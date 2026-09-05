# Stage 1: `unresolved type: BlockValue` in `hir_lowering/module_surface.spl`

Date: 2026-08-21

**Status:** RESOLVED 2026-08-21.

## Answer to the one-bit question

`imported_mod.import_target_indices` for `hir_definitions.spl`'s
`use compiler.blocks.value.{BlockValue}` is **VALID, not -1**. So the defect is
the missing explicit-import step in `resolve_materialized_enum_payload_origin`
(candidate fix 1 of the two below), not surface-registry name resolution.

Evidence, from the driver's own resolution tables:

1. `_driver_resolve_numbered_compiler_import`
   (`src/compiler/80.driver/driver_source_loading.spl:657`) carries an explicit
   rewrite row `compiler.blocks -> compiler/15.blocks/blocks`, so the
   layer-stripped spelling `compiler.blocks.value` resolves to the real file
   `src/compiler/15.blocks/blocks/value.spl`. The short spelling is a
   first-class import spelling, not an accident.
2. `_driver_module_aliases` (`:326`, entry-closure branch) registers a
   `SourceFile` for the CANONICAL name, the WALKED name, and the PHYSICAL name.
   For that file those are `compiler.blocks.blocks.value`,
   `compiler.blocks.value` and `compiler.15.blocks.blocks.value` — three
   distinct registry keys onto one canonical path.
3. `module_surfaces_from_modules` / `add_alias_canonical_identity`
   (`80.driver/driver_source_pipeline_parsing.spl:212`,
   `20.hir/.../module_surface_registry.spl:120`) take exactly that alias branch
   whenever a canonical path repeats, so every one of the three names lands in
   `index_by_name`. `module_surface_resolve_import_key` therefore finds
   `compiler.blocks.value` directly and `module_surface_registry_index` returns
   a valid index.

## Root cause

`resolve_materialized_enum_payload_origin`
(`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:148`)
had exactly two steps: the payload owner's own declarations, then one
`find_reexport_source` hop. `hir_definitions.spl` neither declares `BlockValue`
nor re-exports it — it reaches it with a plain `use compiler.blocks.value.{BlockValue}`
— so both steps missed and the origin came back not-found. Its caller
`register_materialized_payload_named_dependency` (`:228`) then returned
**silently**, nothing was materialized, and the failure resurfaced much later as
the hard `unresolved type: BlockValue` in `hir_lowering/types.spl:811`,
attributed to `module_surface.spl` — an innocent importer of the ENUM that never
names the payload type.

## Fix

Two parts, both in `module_reexport_materialization.spl`:

1. **Third resolution step.** New
   `resolve_materialized_enum_payload_explicit_import` walks the owner's
   `imports` / `import_target_indices` for an explicit named item (honouring
   `as` aliases), taking the declaration directly or one `find_reexport_source`
   hop beyond it. Mirrors the twin step in
   `materialize_imported_callable_explicit_dependency`; glob and package
   inference stay deliberately excluded, because the same short name can live in
   several sibling modules and picking one would silently rewrite the payload
   type.
2. **The silent return is now LOUD.** `register_materialized_payload_named_dependency`
   emits `[hir-payload-origin-unresolved] owner=<owner module> owner_key=<key>
   payload=<type>` naming the real OWNER and the payload type, and states that a
   later `unresolved type` will be blamed on an importing module instead. It is
   advisory (`eprint`, not `self.error`) on purpose: a payload the consumer
   already has in scope is still lowerable, so failing the build there would be
   a regression rather than a fix.

## Regression spec

`test/01_unit/compiler/hir/enum_payload_origin_plain_use_spec.spl` (byte-identical
mirror at `test/unit/compiler/hir/...`). Builds the exact shape by hand —
`pv.value` declares `enum Payload`; `pv.defs` reaches it through a plain,
non-exporting `use pv.value.{Payload}` and owns the enum carrying it — and calls
`resolve_materialized_enum_payload_origin` directly, which is the shape the
harness note below recommends. **Verified RED before the fix** (`✗ ... 1 example,
1 failure`) **and GREEN after** (`✓ ... 1 example, 0 failures`).

## Rejected fixes (both were reverted by the previous pass; disposition now)

1. **Add an explicit-import step** — this is the landed fix. The earlier pass
   reverted it only because its three-module fixture routed a FACADE re-export,
   which `find_reexport_source` already covered, so the fixture was never red.
   Removing the facade and importing the enum directly makes it red.
2. **Rewrite the import in `hir_definitions.spl` to `compiler.blocks.blocks.value`** —
   still rejected, and the evidence above is why: the short spelling is a
   supported rewrite-table spelling that resolves to a valid registry index.

## Harness note (kept; see the sibling bug record)

A spec that drives `lower_module` over an IMPORTED ENUM dies with
`method 'lookup_or_invalid' not found on type 'SymbolTable'`. That is NOT a
second-impl-block defect — see
`doc/08_tracking/bug/symbol_table_second_impl_block_unreachable_interpreted_2026-08-21.md`.
Calling `resolve_materialized_enum_payload_origin` directly, with
`use compiler.hir.hir_lowering.items.*` in the spec so the impl block's own
module is in the closure, is the workable shape and is what the spec does.
