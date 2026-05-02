# CLI Compile Direct SMF

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 0
**Status:** Blocked

## Research

- `src/app/io/cli_compile.spl` imported `compile_to_smf` from the heavy driver module, but did not use a direct SMF helper in the CLI path.
- `compiler.driver.driver_api_compile_single.compile_to_smf(path, output)` is the split Tier 2 single-file facade for direct SMF compilation.
- The facade accepts only source and output paths, so it should only handle the straightforward SMF path. Backend-specific, release, low-memory, native, and target-specific compile modes should keep their existing routes.

## Plan

- Import `compile_to_smf` from `compiler.driver.driver_api_compile_single`.
- Add a small CLI helper that computes the existing default `.simple/build/*.smf` output path and calls the direct API.
- Route only `--format=smf` with default backend and no release/low-memory options through the direct helper.
- Preserve existing behavior for all other compile modes.

## Blocker

- Importing `compiler.driver.driver_api_compile_single.compile_to_smf` into `src/app/io/cli_compile.spl` makes `compile_entry.spl` fail before command dispatch with `error: semantic: method len not found on type nil`.
- The failure reproduces even for `compile --help`, so this direct import cannot be safely landed in the CLI compile entrypoint.
- Leave row 0 open and blocked until the driver API facade import semantic failure is fixed.

## Verification

```sh
bin/simple lint src/app/io/cli_compile.spl
bin/simple run src/app/cli/compile_entry.spl compile --help
```
