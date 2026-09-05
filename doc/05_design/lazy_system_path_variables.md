<!-- codex-design -->

# Lazy system path variables detail design

## Registered names

| Reference | Simple override | OS source/fallback |
|---|---|---|
| `home` | `SIMPLE_SYS_HOME` | `HOME`, then `USERPROFILE` |
| `user_local` | `SIMPLE_SYS_USER_LOCAL` | `LOCALAPPDATA`; macOS Application Support; XDG data |
| `user_cache` | `SIMPLE_SYS_USER_CACHE` | `LOCALAPPDATA`; macOS Caches; `XDG_CACHE_HOME` |
| `user_config` | `SIMPLE_SYS_USER_CONFIG` | `APPDATA`; macOS Application Support; `XDG_CONFIG_HOME` |
| `user_data` | `SIMPLE_SYS_USER_DATA` | `APPDATA`; macOS Application Support; `XDG_DATA_HOME` |
| `user_state` | `SIMPLE_SYS_USER_STATE` | local app data; `XDG_STATE_HOME` |
| `runtime` | `SIMPLE_SYS_RUNTIME` | `TEMP`; `XDG_RUNTIME_DIR`; temp fallback |
| `temp` | `SIMPLE_SYS_TEMP` | `TEMP`/`TMP`; `TMPDIR`; `/tmp` |
| `compiler_cache` | `SIMPLE_CACHE` | `{sys:user_cache}/simple/cache-manager` |

`SystemLocationInputs` is a bounded value record used by both process resolution and tests. All chosen roots are absolute and normalized to `/`. Joining removes duplicate interior separators without rewriting `//server/share` or `C:/` roots.

`LazyPathTemplate.resolve()` scans left to right, recognizes only `{sys:name}`, supports `{{` and `}}` literals, rejects other braces, and memoizes the result. A caller-specific override applies only when the template contains exactly one root system token at its beginning.

`system_path_native` is the required adapter before a canonical value is passed
to a file primitive or used as the executable/working-directory path of a
process primitive. It is deliberately not called while forming cache keys.
The canonical `io_runtime`, `io.file_ops`, and `io.process_ops` owners apply
the adapter to file/directory operands and executable names. Process arguments
remain opaque because an arbitrary argument is not necessarily a path.

## Errors

Stable codes: `unknown_system_location`, `malformed_path_template`, `relative_system_location`, `nul_in_system_location`, and `unsupported_platform_location`.
