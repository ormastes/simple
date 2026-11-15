# nogc_async_mut/fs/flat.spl imports `dir_list` from a facade that renamed it

**Date:** 2026-11-14 **Status:** fixed (this change) **Found by:** bootstrap run 31, Phase 2 `compiler_cli_build`

## Symptom

Full-CLI build with the Stage 2 compiler lowers 3144 of 3145 modules and fails one:

```
HIR lowering error in src/lib/nogc_async_mut/fs/flat.spl: unresolved name: dir_list at src/lib/nogc_async_mut/fs/flat.spl:707:10
HIR lowering error in src/lib/nogc_async_mut/fs/flat.spl: unresolved name: dir_list at src/lib/nogc_async_mut/fs/flat.spl:712:5
[hir-reexport-chase-unresolved] facade=lib.io_runtime item=dir_list ...
```

## Cause

`eaa5bf5f190` (dup-def renames round 2) renamed the `std.io_runtime` export
`dir_list` to `dir_list_or_empty` / `dir_list_optional`. The sync twin
`nogc_sync_mut/fs/flat.spl` was updated. The async twin was not: `05a537db28f`
(gc-layering reroute) rewrote its imports the same day and kept the old name.

## Fix

`nogc_async_mut/fs/flat.spl` now imports and calls `dir_list_or_empty`,
byte-identical to the sync twin for `dir_read` and `dir_is_empty`.
Spec: `test/01_unit/lib/nogc_async_mut/fs/flat_dir_listing_spec.spl`.

## Evidence and its limits

- The spec passes on the Rust seed both before and after the fix. The seed
  binds an unqualified call by name alone across the co-compiled closure, so
  it found `nogc_sync_mut.io.dir_ops.dir_list` and hid the stale import.
- Stage 2 (run 31, `native-build --threads 1 --entry-closure`) on a 4-line
  probe that calls `Dir.read("/tmp")` and `Dir.is_empty("/tmp")`, before the
  fix: the build exits 0 and the binary prints `empty` for a non-empty `/tmp`.
  So in a small closure the unresolved name is not reported at all and the
  call yields a wrong value; only the full-CLI closure reports it as an error.

## Follow-ups (not fixed here)

- **Unresolved facade import can compile silently to a wrong value** (the
  probe above). The `[hir-reexport-chase-unresolved]` note should be an error
  in every closure, not only where a later lookup happens to fail.
- Three more stale `std.io_runtime` imports, all outside the full-CLI closure
  (found by checking every `use std.io_runtime.{...}` under `src/` against the
  facade's export list; these four were the only misses):
  - `src/app/verify/worker.spl:39` imports `read_dir`
  - `src/app/test_runner_new/inprocess_probe.spl:3` imports `file_read_text`
  - `src/app/test_runner_new/preprocess_probe.spl:6` imports `file_read_text`
- Sibling facades, same check (review 2026-11-14; brace, paren and single-name
  imports under `src/` against each facade's declarations). None is called
  from the full-CLI closure: run 31 lowered all 3145 modules and collected
  only the two `dir_list` errors above.
  - `std.nogc_sync_mut.sffi.io` (the same commit renamed its `dir_list` to
    `dir_list_nullable`; it has no plain `file_read_text` either):
    - `src/lib/nogc_sync_mut/ffi/io.spl:16` re-exports `file_read_text`. This
      module IS in the full-CLI closure; run 31 printed the
      `[hir-reexport-chase-unresolved]` note for it and no error, because no
      closure module consumes that name through `ffi.io`.
    - `src/lib/nogc_async_mut/sffi/io.spl:7` re-exports `dir_list`,
      `file_read_text`, `file_modified_time`, `file_mmap_read_text`, `path_join`.
    - `file_read_text` importers: `src/compiler/35.semantics/lint/remote_exec_lint.spl:24`,
      `src/app/test/browser_interaction_capture.spl:20`,
      `src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl:9`,
      `src/os/crypto/x25519_mlkem768/metal_ntt_provider.spl:6`.
    - `src/compiler/80.driver/project.spl:325` calls `dir_list(parent)` and
      tests the result against nil, through `use std.sffi.io*`.
  - `std.nogc_sync_mut.io_runtime`: `src/app/tools/rt_migrate/main.spl:29`
    imports `file_write_text`.
  - `std.nogc_async_mut.io_runtime`: no stale importer.
- The seed's by-name binding hides this class from every interpreter-run spec.
