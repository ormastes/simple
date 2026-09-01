# Native-project aliased `src.std.platform` facade owner loss

- Date: 2026-08-03
- Status: open
- Bug ID: `native_project_src_std_platform_alias_owner_loss_2026_08_03`
- Severity: P2
- Owner: unassigned; recorded separately from the Stage 4 fatal HIR fix

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

No source fix is claimed here. The eventual owner must first decide whether
leading `src.std` is supported import syntax that native-project must normalize,
or whether both filesystem variants should use their direct family platform
facades. Either choice must keep exact owner selection and the strict runtime
regressions above.
