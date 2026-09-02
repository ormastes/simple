# PR #255 `host_path_native` corrupts POSIX filenames and taxes every Unix file op

Status: OPEN. Found 2026-09-02 by measurement on Windows 11 (seed `bin/simple.exe`,
16,347,136 bytes, 2026-09-01 17:54). Engine: `run` = Cranelift JIT.

## Where

`src/lib/nogc_sync_mut/fs/host_path.spl` (new in PR #255, OPEN, head `54ab7186f67`).
Wired into **every** operation in `src/lib/nogc_sync_mut/io/file_ops.spl`:
`rt_file_exists`, `rt_file_read_regular_no_follow_bounded`, `rt_file_write_text_at`,
`rt_file_write_bytes`, `rt_file_atomic_write`, `rt_file_size`, `rt_file_stat`,
`rt_file_hash_sha256` — each calls `host_path_native(path)` first.

## Defect 1 — POSIX path corruption (correctness, severe)

`host_path_native_for` runs `host_path_canonical(path)` = `path.replace("\\", "/")`
**unconditionally, before** the platform check. A backslash is a LEGAL character in
a POSIX filename, so on Linux/macOS the conversion rewrites real filenames.

Measured, byte-for-byte:

| input | output |
|---|---|
| `/home/a\b.txt` (13 bytes) | `/home/a/b.txt` (13 bytes) |

**The length is identical**, so a length-only assertion cannot see this. The result
is that a Linux file op on any path containing `\` silently addresses a different
file. This is the exact hazard for which the dead `unix_to_windows` trio was
deleted on 2026-09-01; `to_native_path` in `platform.spl` deliberately uses
IDENTITY as its non-Windows branch for this reason.

## Defect 2 — Unix overhead (violates the stated NFR "no overhead on linux")

The `.replace()` scan+alloc happens before the guard, and the guard itself
(`_host_is_windows`) calls `.lower()` (an allocation) plus four `.contains()` scans.
Min-of-3 wall, 5,000,000 iterations each, same box, same seed:

| variant | min wall | note |
|---|---|---|
| PR #255 shape (`.replace()` then `.lower()` + 4x `.contains()`) | **11,688 ms** | current code |
| replace-first, cheap literal guard | 6,516 ms | |
| guard-first, cheap literal guard | 2,511 ms | |
| bare function call, no conversion | 907 ms | |
| **cached bool guard, identity early-return** | **421 ms** | the floor |

**~28x** the floor, roughly **2.25 us per call**, paid on every file operation on
Linux. Caveat, stated rather than hidden: the cached-bool variant measures below
the bare-call variant, which indicates the JIT eliminates part of it — that is the
desired outcome, but it means 421 ms is a floor, not a precise per-call cost.

## Defect 3 — drive-letter case conflicts with the specified conversion

Specified: `/d/foo/bar` -> `d:\foo\bar`. Measured output: `D:\foo\bar` (`.upper()`
in `_mingw_drive_to_windows`). Windows treats these equivalently; test fixtures and
log comparisons do not. Needs an explicit decision, then consistency.

## Defect 4 — relative path with a single-letter first segment becomes a drive root

`_mingw_drive_to_windows` admits a compact `c/rest` spelling. Measured:
`c/foo` -> `C:\foo`. A relative directory literally named `c` is rewritten to the
root of drive C:. Combined with `rt_file_atomic_write` this is a data-loss shape.

## Fix sketch (not applied)

1. Make the platform decision the FIRST statement and return `path` unchanged on
   the non-Windows branch — no `.replace()`, no `.lower()`, no scan, no alloc.
2. Hoist the platform decision to a computed-once value; do not call
   `rt_platform_name()` + `.lower()` per path.
3. Move `host_path_canonical` (`\` -> `/`) INSIDE the Windows branch. It is only
   ever correct there.
4. Drop the bare `c/rest` rule, or require an absolute context for it.
5. Decide drive-letter case and pin it with a byte-length + byte-content spec.

## Related

- `doc/08_tracking/bug/lexer_drops_backslash_escape_in_string_literal_2026-09-02.md`
- `src/lib/nogc_sync_mut/platform.spl` `to_native_path` (identity on non-Windows)
- `src/lib/common/path_pure.spl` `to_slash` / `to_backslash`

## Defect 5 — no spec covers `host_path_*` itself

PR #255 adds two specs (`system_location_spec.spl`, `lazy_path_literal_spec.spl`);
neither exercises `host_path_canonical` / `host_path_native_for` /
`host_path_native`. The function is now on the path of every file operation AND
every process spawn (`_io_runtime_process_spawn_async_raw`,
`_io_runtime_process_run_timeout_raw`, `rt_file_rename`, `rt_file_move`,
`rt_dir_remove_all`) with zero direct coverage.

## Census — `c:\`-style literals in `src/**/*.spl`

Method note: the `grep` on PATH and the shell both collapse backslash needles
(a `'C:\'` single-quoted assignment measured `${#N}` = 3, not 4), which produced
two wrong counts before this one. The trustworthy method is `git grep -P` with
**hex escapes**, so no backslash appears in the pattern at all:

```
git grep -nIP '[A-Za-z]:\x5C\x5C' -- 'src/**/*.spl'
```

Result: **38 lines across 21 files**. Most are `:\n` escaped-newline artifacts in
generated-code string builders, not paths. The genuine drive-letter path literals
are **7 lines in 5 files**:

| file:line | literal | lexes to |
|---|---|---|
| `src/app/test_runner_new/test_runner_async.spl:46` | `"C:\Temp"` | **`C:Temp`** (corrupt) |
| `src/compiler/70.backend/linker/link_deps.spl:159` | `"C:\Windows\System32\{lib}.dll"` | **corrupt** |
| `src/compiler/70.backend/linker/link_deps.spl:160` | `"C:\Windows\SysWOW64\{lib}.dll"` | **corrupt** |
| `src/compiler/70.backend/linker/msvc.spl:236` | `"C:\Program Files (x86)\...\vswhere.exe"` | **corrupt** |
| `src/compiler/70.backend/linker/msvc.spl:323` | `"C:\Program Files (x86)\Windows Kits\10\Lib"` | **corrupt** |
| `src/app/llm_caret/.../PowerShellTool/pathValidation.spl:4` | `"...C:\\"` | `C:\` (OK, trailing) |
| `src/app/wine_process_session_plan/main.spl:37` | `"C:\\"` | `C:\` (OK, trailing) |

The five marked corrupt are **broken today, independent of PR #255** — a trailing
`\` lexes correctly, an embedded one does not (measured: `"C:\Temp"` -> 6 bytes
`C:Temp`; `"C:\Windows\System32"` -> 17 bytes `C:WindowsSystem32`). Under the
user's rule ("no `c:\` style path in code; only mingw/linux style") all seven are
violations regardless.
