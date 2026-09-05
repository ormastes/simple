<!-- codex-design -->
# Module Surface Export Provenance Detail Design

## Interfaces

- `ModuleSurfaceExportOrigin`: canonical owner surface index, original owner
  name, declaration kind, immediate source surface index.
- `ModuleSurface.reexports`: public name to origin.
- `module_surfaces_resolve_reexports(input) -> Result<ModuleSurfacesByName,text>`:
  deterministic post-builder finalizer.
- `module_surface_export_origin(surfaces, facade_index, public_name) ->
  ModuleSurfaceExportOrigin?`: allocation-free consumer lookup.
- `module_surface_resolve_key(surfaces, spelling, context_index) -> i64?`:
  shared absolute/relative/package/tier alias resolution.

## Algorithm

Use surface array order as the stable traversal order. Build explicit candidate
edges first from `ParserImport` plus `Export` metadata, decoding `source:local`
once. For globs, iterate surfaces until no new edge is added. Track
`Unvisited/Visiting/Resolved/Failed` per `(surface, public_name)` during
recursive resolution. Same canonical owner/name coalesces; different canonical
owners produce ambiguity. A cycle with no direct declaration fails.

Do not iterate dictionary keys to choose winners. Never use `Dict.get()` for
native integer indices; use `contains_key` plus bracket access.

## Integration

Finalize in streaming parsing, retained module rebuild, and C-entry surface
construction. `register_imported_symbol` checks direct declarations, then the
map. Glob registration enumerates direct public names plus re-export map names
and calls the same registration path. Fallback calls to
`find_reexport_source` increment a debug counter and cannot silently change a
resolved or ambiguous result.

## Errors

Diagnostics include facade module/path, public name, edge spelling, and
canonical candidates. Missing target, non-public target, cycle, ambiguity, and
invalid index are separate stable categories.

## Migration

Slice 1 adds map/finalizer and focused tests. Slice 2 routes explicit imports.
Slice 3 routes glob imports and compares Stage 4 fan-out. Slice 4 removes the
legacy chase after fallback count is zero. Later phases introduce
`ResolvedModuleGraph` and symbol-body closure without changing the immediate
origin lookup contract.
