# Loader: sibling-file `export` cannot be moved to `__init__.spl` (interpreter-mode resolution)

- **Date:** 2026-04-28
- **Reporter:** Stream B2 (lint recovery — loader exports)
- **Status:** Open / Architectural conflict

## Summary

The lint guidance asks for `export ...` declarations to live in `__init__.spl` only, not in sibling .spl files inside a package. Following that rule for the three flagged files would silently break runtime imports because the interpreter does not resolve sibling-file symbols re-exported from `__init__.spl`.

## Affected files (TODOs flagged for "move exports to __init__.spl")

- `src/lib/debug.spl` — `export DebugLevel, StepMode, Breakpoint, StackFrame, Debugger`, `export debugger_new, level_to_int, should_print, debug_print, handle_debug_command`
- `src/lib/platform.spl` — `export is_windows, is_unix, is_macos, is_linux`, `export get_host_os, get_host_arch, dir_sep, path_sep, exe_ext, lib_ext`, `export normalize_path, is_absolute_path, join_path, resolve_command`
- `src/lib/nogc_sync_mut/debug.spl` — `export DebugLevel, StepMode, Breakpoint, StackFrame, Debugger`, `export debugger_new, level_to_int, should_print, debug_print, handle_debug_command`

## Primary-source evidence

`src/lib/__init__.spl:351-357` already attempted the move and reverted it. The relevant block:

```
# Re-exported from platform.spl
# NOTE: These symbols come from sibling shim platform.spl which glob-imports
# from nogc_sync_mut.platform, but sibling file symbols are not in __init__
# scope in interpreter mode. Access via `use std.platform.{is_windows}` etc.
# export is_windows, is_unix, is_macos, is_linux
# export get_host_os, get_host_arch
# export dir_sep, path_sep, exe_ext, lib_ext
# export resolve_command
# export normalize_path, is_absolute_path, join_path
```

`src/lib/nogc_sync_mut/__init__.spl` carries the equivalent NOTE for the same root cause. Someone tried the move, found it broken, commented out the exports, and left a NOTE telling callers to use `use std.platform.{is_windows}` directly.

## Architectural conflict

- **Lint rule wants:** exports only in `__init__.spl`.
- **Interpreter-mode resolution requires:** exports to stay in the sibling source files for `use std.platform.{X}` to find `X` at runtime.

These two are incompatible until interpreter-mode `__init__.spl` re-exports of sibling-file symbols are fixed at the loader level.

## Proposed fixes (out of B2 scope)

1. **Compiler/loader:** make `__init__.spl` re-exports of sibling-file symbols visible in interpreter mode (matching compiled-mode behavior).
   - File: `src/compiler/99.loader/loader/module_loader.spl` and the resolver layer.
2. **OR Lint rule:** update the lint that flags sibling-file `export` lines so it accepts shim modules that re-export from a depth-prefixed companion module (e.g. `std.platform` is a shim around `nogc_sync_mut.platform`).
   - File: `src/lib/common/tooling/easy_fix/rules_lint.spl`.

## Workaround applied (B2)

- `export` lines in the three source files are **preserved** (they are load-bearing for interpreter-mode resolution).
- TODO comments in those files are updated from "move these to __init__.spl" to a brief note pointing at this bug doc.
- `__init__.spl` re-export blocks remain commented out with their existing NOTE intact.
- Lint findings for these three files are unchanged by design.
