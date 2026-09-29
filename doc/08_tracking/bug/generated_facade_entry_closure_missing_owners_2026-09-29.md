# Generated facade origins require their physical owners in the entry closure

## Actual retained failure

Linux source6772d23f5e2, emitted pure producer SHA256
569203737fe7bdfafd6f52cfe1c1c8d6a30ed17b741217a08c267058e2f8283c,
failed HIR after parsing 1017 physical modules. The retained authoritative
native-build-stderr-532969-1.log has 369 invalid-export-origin textual messages
under seven compiler.frontend.core facade owners: backend_types144, error108,
alloc_inference36, call_graph36, closure_analysis36, hir_types5 and mir4.
All seven actual core owner files were absent from all 1017 released surface
receipts, while core/__init__.spl was committed. Repeated text is not counted
as independent root causes. The original failed artifacts remain untouched.

## Narrow correction

The common generated_facade_export_pairs scanner supplies the same finite
owner/export pair projection to driver sibling discovery and HIR provenance.
It requires a top-level paired bare export and excludes docstrings, unpaired
markers, unrelated declarations, explicit export-use/export-from routes and
glob-only declarations. Existing named-import origins still override generated
provenance in the unchanged export-origin resolver. No facade exports are
pruned and missing owners still reach the normal unresolved-import failure.

Compiler-owned loading now consumes cached siblings like the native CLI walk.
Relative dependency keys include their importing directory, and a relative
spelling is not published as a global module alias: two facades' `.owner`
dependencies must remain distinct. HIR already resolves relative imports
against the importer when there is no raw global leading-dot alias.
Relative dependencies never fall back to unrelated --source roots when their
local owner is missing; non-relative module fallback keeps its existing policy.
The scoped relative resolver also avoids cwd/src probes before the local owner
and returns its miss directly instead of entering the global exact resolver.

## Focused fixtures; execution pending root review and corrected producer

- generated_facade_provenance_check.spl has concrete owner/item assertions and
  rejects docstring, dangling, unrelated, explicit-route, glob-only, expression
  and indented pseudo-export cases; quoted comments do not open docstrings.
- fixtures/generated_facade_closure/main.spl imports a callable, enum and
  constant through real generated facade exports. A competing real named import
  must win (22 rather than11). A second facade with its own `.owner` returns73.
  The first owner calls an explicitly imported leaf, exercising transitive
  closure discovery. Run compiler-owned loading with unrelated_source_root as
  cwd too: its real owner.spl returns wrong values and must never shadow local.
- fixtures/generated_facade_closure/missing_owner.spl intentionally references
  an absent provenance owner. Its entry-closure build must fail with the normal
  owner-resolution diagnostic and must not produce an admitted executable.
  Include unrelated_source_root as an additional source root: its real
  absent_owner.spl exports missing_call but must not satisfy the local owner or
  appear among loaded closure sources. This checks resolution, not just exit.

After source review, use an exact refreshed pure-Simple producer and private
per-entry/per-phase caches. Compile and run the two positive fixture entries
once, checking exact markers GENERATED_FACADE_PROVENANCE_COMPONENT_PASS and
GENERATED_FACADE_CLOSURE_COMPONENT_PASS with exit0; compile the missing-owner
entry once and require failure naming absent_owner. Exercise compiler-owned
explicit-entry loading as well as CLI closure discovery before claiming route
agreement. Native execution has not occurred; this is not bootstrap admission
or a memory-retention qualification.
