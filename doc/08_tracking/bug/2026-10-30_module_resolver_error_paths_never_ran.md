# Module resolver error and constructor paths could not run

- Status: FIXED 2026-10-30
- Component: `src/compiler/99.loader/module_resolver/{resolution,manifest}.spl`
- Found by: post-merge review of PR #5333 (`cached_directory_resolution_spec` 0/4 on the seed)

## Symptom

Once the seed gained `clone()` (PR #5365), the spec still failed, one defect at a time:

1. `unknown static method directory/file on class ResolvedModule`: `resolve_from_base`
   called `ResolvedModule.directory(...)` / `.file(...)`, but those were desugared to
   the free functions `resolvedmodule_directory` / `resolvedmodule_file` in `types.spl`.
2. `method 'with_note' not found on value of type enum`: `CompileError` has no
   `with_note`; only `ErrorContext` does. 4 sites in `resolution.spl`, 1 in `manifest.spl`.
3. `missing return in non-unit function 'resolve'`: functions declared
   `-> T | CompileError` returned a bare `CompileError` while callers `match` on
   `Ok/Err`, so no arm matched. 7 sites in `resolution.spl`, 3 in `manifest.spl`.

Every unresolved import therefore failed inside the resolver instead of returning an
error, and every successful file/directory resolution failed on the constructor.

## Fix

Call the free constructors; build notes through
`CompileError.<kind>_with_context(msg, ErrorContext.empty().with_note(...))`; wrap
every error return in `Err(...)`, matching the existing `Ok(...)` returns.

## Specs

- Reproducer: `test/01_unit/compiler/module_resolver/cached_directory_resolution_spec.spl` (0/4 -> 4/4)
- Generalisation: `test/01_unit/compiler/module_resolver/tier_ambiguity_warning_spec.spl`
  now drives `ModuleResolver.resolve` end to end (replaces its source-text scan);
  `numbered_last_segment_single_scan_spec.spl` 1/3 -> 2/3 (remaining failure is the
  unrelated `FileMode.ReadOnly` seed gap).
- The capability-violation path in `manifest.spl` cannot run on the seed
  (`Parser.new` is unknown there); it is covered only by compilation.
