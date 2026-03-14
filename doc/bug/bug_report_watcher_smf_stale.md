# Bug Report: Watcher does not invalidate/regenerate SMF when SPL source changes

**Bug ID:** WATCHER-SMF-001
**Date:** 2026-03-14
**Severity:** P2 - Medium (causes stale compiled modules to shadow source edits)
**Component:** Watcher — File Change Handler
**Status:** Fixed (2026-03-14) — SMF deleted on .spl change in process_file_changes()

## Summary

When `.spl` source files are modified, the watcher daemon (`watcher_daemon.spl`) only regenerates SHB files but does NOT invalidate or regenerate corresponding `.smf` compiled modules. This causes stale `.smf` files to shadow updated `.spl` sources when the module loader prefers `.smf` over `.spl`.

## Reproduction

1. Have a working `.spl` module with a corresponding `.smf` compiled version
2. Edit the `.spl` source file (e.g., change a struct field type)
3. Run the module via interpreter mode (`bin/simple build <command>`)
4. **Result:** The interpreter loads the stale `.smf` instead of the updated `.spl`, executing old code

## Observed in Practice

The `duplicate-check` tool at `src/app/duplicate_check/` had stale `.smf` files (dated Feb 25) while the `.spl` sources (symlinked to `src/compiler/90.tools/duplicate_check/`) were edited. The interpreter loaded the stale `.smf` files, ignoring source changes. Stale `.smf` existed at BOTH the symlink location and the actual source location.

## Root Cause

In `src/compiler/80.driver/watcher/watcher_daemon.spl`, the `process_file_changes()` method detects `.spl` changes but only triggers SHB generation — no SMF invalidation or regeneration.

The cache validator (`cache_validator.spl`) has hash-based validation logic that CAN detect stale SMF, but the watcher never triggers this validation or SMF regeneration.

## Expected Behavior

When a `.spl` file changes, the watcher should either:
1. Delete the corresponding `.smf` file (forcing re-interpretation from source), OR
2. Regenerate the `.smf` from the updated `.spl` source, OR
3. At minimum, mark the `.smf` as stale so the loader falls back to `.spl`

## Workaround

Manually delete stale `.smf` files:
```bash
rm src/app/duplicate_check/*.smf
rm src/compiler/90.tools/duplicate_check/*.smf
```

## Related

- `INTERP-DICT-001` — dict type annotation bug was masked by stale `.smf` loading
- `src/compiler/80.driver/cache/cache_validator.spl` — has hash-based validation (unused by watcher)
- `src/compiler/99.loader/loader/module_loader.spl` — module loader SMF preference logic
