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
