# Compatibility loader leaks partial executable mappings on load failure

Status: fixed (2026-11-03)

## Evidence

`src/compiler/99.loader/module_loader_compat.spl` allocates and publishes each
symbol mapping inside the load loop. Later failures from code copy, protection
transition, symbol-table parsing, relocation resolution/bounds, or metadata
loading return immediately without releasing mappings already created by the
transaction or removing their provisional global-symbol entries.

This is source-proven retained executable memory and stale publication risk.
Runtime bytes/RSS were not measured because the production self-hosted binary
is unavailable in this worktree; no numeric impact is claimed.

## Required fix

- Keep candidate mappings private until every symbol and relocation validates.
- On every failure, unmap each candidate exactly once and remove provisional
  symbol state.
- Publish the module/global symbol set atomically only after validation.
- Preserve the current single-pass code-copy and relocation hot paths; rollback
  bookkeeping may allocate only once per load transaction, not per relocation.

## Acceptance evidence

- sabotage fixtures for copy, `mprotect`, unresolved symbol, relocation bounds,
  and metadata failures;
- mapping count/bytes and global-symbol state return to their pre-load values;
- successful-load timing, allocation count, and peak RSS do not regress beyond
  the repository's loader threshold.

## Resolution (2026-11-03)

`module_loader_compat.spl` load now keeps a one-array rollback ledger of
candidate mappings (code + GOT), unmaps each exactly once through
`_compat_load_fail` on every failure, and publishes `global_symbols` only after
all relocations validate. Spec: `test/01_unit/compiler/loader/module_loader_partial_mapping_rollback_spec.spl`
(budget 0 leaked mappings / bytes / global symbols; fails before fix with
leak=1). Not covered: `unload` of a successful module still never frees its
exec mappings (existing lifetime contract, noted in the loader source).
