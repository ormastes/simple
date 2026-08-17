# Native-project aliased `src.std.platform` facade owner loss

- Date: 2026-08-03
- Status: source fixed; focused Rust test execution blocked by an unrelated macOS test cfg error
- Bug ID: `native_project_src_std_platform_alias_owner_loss_2026_08_03`
- Severity: P2
- Owner: Codex `/root/p2_native_alias`; recorded separately from the Stage 4 fatal HIR fix

## Exact cycle-3 evidence

The x86 Stage 4 cycle-3 build at revision `98354c3a0c5` completed far enough to
emit these two nonfatal diagnostics in
`/tmp/simple-stage4-final-20260803/build/stage4-final/build.log`:

```text
warning: unresolved call `platform_normalize` in function `src__lib__nogc_sync_mut__fs__Path.normalize` (module: src__lib__nogc_sync_mut__fs)
warning: unresolved call `platform_normalize` in function `src__lib__nogc_async_mut__fs__Path.normalize` (module: src__lib__nogc_async_mut__fs)
```

This is one category, not two independent bugs. The affected physical files
are `src/lib/nogc_sync_mut/fs.spl` and
`src/lib/nogc_async_mut/fs.spl`; their `src/std/...` copies are hardlinks.

## Root cause

Both files import through the legacy shim spelling at line 22:

```simple
use src.std.platform (is_windows, dir_sep, normalize_path as platform_normalize, is_absolute_path as platform_is_absolute, join_path)
```

`src/std/platform.spl` glob-re-exports `nogc_sync_mut.platform`, which in turn
re-exports path operations from `nogc_sync_mut.path`. In the Rust native-project
pipeline, `collect_use_imports` recognizes the aliased group member, but
`resolve_import_name_strict` searches facade prefixes derived from normalized
segments `src`, `lib`, `platform`. Those prefixes do not identify the retained
shim/re-export owner. Project-wide `normalize_path` declarations also exist in
the no-GC async, no-GC sync, and GC path providers, so the unique-candidate
fallback correctly refuses to guess. `platform_normalize` is omitted from the
per-module use map and `mangle.rs::resolve_call_target` reports it unresolved.

`platform_is_absolute` follows the same alias and facade route and is therefore
a latent member of this category. It was not present in the captured warning
pair because its caller was not retained/reached by that build slice.

## Impact and candidate sanity

The warnings are nonfatal while the affected methods are unreachable and their
sections are discarded, so basic CLI help/version sanity is not evidence that
the calls work. A candidate or feature that reaches `Path.normalize` or
`Path.is_absolute` can instead expose a strict-link failure, forbidden stub
fallback, or wrong-provider dispatch. Do not waive this category for filesystem
feature sanity merely because the basic candidate starts.

## Focused regression plan

1. Add a Rust native-project import-map test using three duplicate path
   providers, the platform shim plus its transitive facade, and the actual
   aliased group import. Assert `platform_normalize` and
   `platform_is_absolute` map to the exact retained path-owner mangled symbols
   for both no-GC filesystem families, with no suffix-based guess.
2. Add a strict native fixture for each family that calls `Path.normalize` and
   `Path.is_absolute`. Build with `SIMPLE_NO_STUB_FALLBACK=1`, assert stderr has
   neither unresolved-call nor generated-stub diagnostics, execute the binary,
   and check normalized-path and absolute-path results.
3. Include an adjacent control with multiple same-named providers so the test
   proves facade provenance rather than accidental global uniqueness.

## Fix boundary

The pure-Simple owners now import their family facades directly:

- `nogc_sync_mut.fs` uses `std.nogc_sync_mut.platform`.
- `nogc_async_mut.fs` uses `std.nogc_async_mut.platform`, whose compatibility
  facade explicitly delegates to `std.nogc_sync_mut.platform` and therefore to
  the canonical sync path owner.

This proves the correction belongs above the Rust boundary: the legacy
`src.std.platform` shim is an interpreter compatibility spelling and already
delegates to the sync family. Native-project does not need to guess among
duplicate path providers once each pure-Simple filesystem family names its
owned facade. No Rust production code changed.

## Regression coverage

- Exact: `native_project_fs_platform_aliases_keep_the_sync_path_owner` loads the
  production sync/async filesystem, platform, path, and legacy shim sources and
  requires both aliases in both filesystem families to bind to the canonical
  sync path symbols.
- Adjacent: `aliased_family_facade_rejects_adjacent_duplicate_path_owner`
  introduces a GC decoy with both same-named functions and proves the family
  facade selects the sync owner instead of relying on global uniqueness or
  discovery order.

The first focused command exposed an adjacent test-harness defect: an ungated
macOS test called Linux-only `build_compiler_backfill_test_archive`. The test is
now Linux-gated like the helper and its neighboring archive tests. After that
correction, both focused regressions execute on this macOS host:

```text
cargo test -q -p simple-compiler --lib native_project_fs_platform_aliases_keep_the_sync_path_owner
# PASS: 1 passed
cargo test -q -p simple-compiler --lib aliased_family_facade_rejects_adjacent_duplicate_path_owner
# PASS: 1 passed
```

`cargo check -p simple-compiler --lib` also passes. No admitted pure-Simple CLI
exists in this worktree, so the historical cycle-3 warnings remain the exact
end-to-end executable reproduction evidence; a seed or stale binary was not
substituted for final native-project admission.

## Knowledge update scope

- Feature and layer expert notes updated for the family-facade ownership rule.
- `doc/07_guide/`: N/A; this is an internal native-project/pure-Simple import
  ownership correction, not a user-facing reachable capability or command.
- Research/architecture/design/plan: N/A; behavior and module boundaries are
  unchanged.
- Workflow/SPipe/manual docs: N/A; no workflow or SSpec surface changed.
