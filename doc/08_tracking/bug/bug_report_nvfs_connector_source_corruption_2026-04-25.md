# Bug Report: nvfs_connector.spl source on disk corrupted (74 placeholders)

**Bug ID:** B-VFS-NVFS-CONN-SRC
**Date:** 2026-04-25
**Severity:** P2 - Medium (blocks AC-4 verification; not a runtime bug)
**Component:** `src/os/services/vfs/nvfs_connector.spl`
**Status:** Open, pre-existing — surfaced by sstack/log-lib-drivers Phase 7

## Summary

The on-disk source of `src/os/services/vfs/nvfs_connector.spl` contains
74 `/* complex expr */` placeholders in the `_log_warn` and `_log_error`
helper bodies. The placeholders look like serialization artifacts from
an editor that lost context expressions during a save/round-trip.

This corruption pre-dates the log-lib-drivers feature: it was committed
in `0515a3d0b7` (before `log-lib-drivers` Phase 1 began). The Phase 6
refactor migrated `vfs_service.spl` cleanly but had to leave
`nvfs_connector.spl` untouched because the placeholders cannot be
reconstructed from the diff alone.

## Acceptance Criteria Impact

`AC-4` of the log-lib-drivers feature requires "all SimpleOS
driver-level logging routes through the unified facade", and Phase 3
§G named `nvfs_connector.spl` as one of the targets (alongside
`vfs_service.spl`). The migration cannot be performed on a file whose
helper bodies are placeholders.

Marked as PARTIAL (`[~]`) in the Phase 7 final AC table:

> AC-4: x86_64 + arm64 + riscv32 + riscv64 + vfs_service migrated;
> nvfs_connector blocked by pre-existing source corruption (B-VFS-NVFS-CONN-SRC).

## Reproduction

```bash
grep -c '/\* complex expr \*/' src/os/services/vfs/nvfs_connector.spl
# → 74
```

## Plan

1. Recover the original `nvfs_connector.spl` either by:
   a. Tracing back through the git history before `0515a3d0b7` to find
      a working snapshot, OR
   b. Rewriting `_log_warn` / `_log_error` from the surrounding
      callsites + the architectural intent.
2. Once recovered, apply the same Phase 6 migration that landed for
   `vfs_service.spl` (commit `934e419457`): drop the local log shims
   and `use os.kernel.log.klog_api.{log_info, log_warn, log_error}`.
3. Re-run the smoke spec at
   `test/integration/simpleos_driver_log_smoke_spec.spl` once it can
   meaningfully execute end-to-end.

## Links

- Pre-existing commit: `0515a3d0b7`.
- Phase 6 sibling migration: `vfs_service.spl` → commit `934e419457`.
- Phase 7 verify report: `.sstack/log-lib-drivers/state.md` §7-verify.
