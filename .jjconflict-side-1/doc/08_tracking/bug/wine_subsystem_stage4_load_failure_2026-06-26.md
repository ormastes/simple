# Bug: Wine subsystem — all 127 specs fail (missing source modules)

**Date:** 2026-06-26
**Status:** RESOLVED (74 files restored from git history; 13 files have no history)
**Severity:** P2 (large feature gap, no regression — never worked)
**Classification:** both-seed-and-stage4 / missing-source → DELETED-AND-RESTORED

## Summary

**RESOLVED:** 74 of 87 wine library source files have been restored from git
history (commit range 25a60a1eba5c, c3638484a2d0, and others). The remaining
13 files were never committed to git and have no recoverable history. The
restored files are staged for commit under `landing id: wine-restore`.

## Restoration Details (2026-06-26)

**74 files restored from git history:**
- `src/lib/common/pe_coff_header.spl` (restored from 25a60a1eba5c)
- `src/lib/common/wine_advapi32_*.spl` (4 files)
- `src/lib/common/wine_dll_*.spl` (13 files)
- `src/lib/common/wine_kernel32_*.spl` (20 files)
- `src/lib/common/wine_nt_*.spl` (11 files)
- `src/lib/common/wine_ntdll_*.spl` (8 files)
- `src/lib/common/wine_posix_adapter.spl`
- `src/lib/common/wine_user32_window.spl`
- `src/lib/common/ui/wine_*.spl` (2 files)
- Other wine_* modules (14 files)

**13 files with NO git history (never committed):**
- wine_posix_bridge.spl
- wine_posix_fd_adapter.spl
- wine_posix_handle_table.spl
- wine_posix_thread_adapter.spl
- wine_session_context.spl
- wine_subsystem_guest_debug.spl
- wine_subsystem_host_debug.spl
- wine_subsystem_module_inventory.spl
- wine_subsystem_runtime_heap.spl
- wine_subsystem.spl
- wine_user32_dialog.spl
- wine_user32_message.spl
- wine_xlib_bridge.spl

These 13 files will need to be reimplemented or sourced from another origin if they
are required for wine subsystem completeness.

## Original Error (pre-restoration)

```
error: semantic: Cannot resolve module: common.pe_coff_header
[WARN] Failed to load imported types from ["common", "pe_coff_header"]:
  Module resolution error: cannot resolve import: module path segment `common`
  not found
  help: check that the module exists at
        "test/01_unit/lib_standalone/common/common"
```

The resolver looks for `common/wine_pe_loader_runtime.spl` relative to the
spec file's directory (a standalone layout), but the source lives under
`src/lib/common/` and was not present there at all.

## Notes

- The integration specs (`test/02_integration/app/wine_hello_command_spec`,
  `wine_hello_log_modes_spec`, etc.) have pre-compiled `.smf` stubs in
  `.simple/build/` but their source is also absent.
- The `wine_hello.smf` app image in `build/test-artifacts/` is a pre-built
  binary artifact unrelated to the missing source library.
- The standalone test layout (specs import `use common.*` without `std.`)
  relies on `src/lib` being on the module search path, which requires the
  correct resolver configuration in `test/01_unit/lib_standalone/`.
