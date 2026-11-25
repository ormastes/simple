# Taskbar pin persistence was not transactional

- **Status:** fixed; live native persistence evidence blocked by VFS global lowering
- **Affected owner:** `DesktopShell.pin_app` / `DesktopShell.unpin_app`

## Root cause

Both mutations changed the in-memory ordered pin arrays, called
`save_pinned_layout()`, ignored its result, and returned success. A storage
failure therefore exposed state that could not survive restart.

## Fix

Pin now removes the appended record if persistence fails. Unpin restores the
prior arrays if persistence fails. Both return `false`, preserve ordered stable
`app_id` state, retain the persistence error counter, and restore the prior
`pinned_layout_persisted` truth value.

## Evidence

The focused SSpec covers failed pin and failed unpin rollback, persisted unpin,
and close removing the running taskbar entry. A pure-Simple Stage-2 native
closure compiled the probe, but the build generated unresolved stubs and the
binary faulted in cross-module `g_mount_table` access inside
`g_vfs_write_file_text`. That run is rejected as runtime evidence; it records
the existing module-global aggregate compiler blocker rather than a WM pass.
A final `SIMPLE_NO_STUB_FALLBACK=1` build failed closed on unresolved VFS,
logging, FAT32, and panic owners, so no stubbed executable is admitted.

## Verification 2026-11-25 (work/p3-bao-20261125)

Fix confirmed present on current source, exactly as the Fix section
describes: `src/os/desktop/_DesktopShell/shell_workspace_methods.spl`
`pin_app` (lines 16-26) rolls back the appended id/name/icon entries and
restores the prior `pinned_layout_persisted` when `save_pinned_layout()`
fails; `unpin_app` (lines 51-57) restores the prior arrays and persisted
truth value on failure; `save_pinned_layout` (lines 71-92) increments
`pinned_layout_error_count` and returns false on write failure.

The focused SSpec `test/01_unit/os/desktop/shell_taskbar_pin_spec.spl`
exists but is NOT runnable under the pinned tracked seed on this Windows
host: the spec load errors before any example executes (verdict
`outcome=ERROR declared>=3 executed=0`) on W-STR-BRACE-001 brace-escape
handling in the unrelated generated module
`src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl:9` pulled in by
the import closure — a seed loader limitation, not a pin-logic failure.
Verification here is therefore by code inspection only; the live native
persistence evidence remains blocked as the status line records.
