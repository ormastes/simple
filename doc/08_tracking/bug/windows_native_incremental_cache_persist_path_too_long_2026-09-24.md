# Windows native-incremental cache never persists: object path exceeds MAX_PATH

**Status:** Fixed 2026-09-24.

## Symptom

Stage-2 Windows verification (`compiler_cli_build` task,
`.simple/storage/build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/compiler_cli_build.log`)
printed the same message 2,296 times:

```
[native-incremental] cache write skipped for <file>: persist cache object: The system cannot find the path specified. (os error 3)
[native-build] compiled=2298 reused=0 failed=30
```

Every rerun of the ~11-minute full-CLI native-build recompiled all 2,298 files
from scratch — the object cache was write-only-failing, so `reused` was
permanently stuck at 0.

## Root cause

`persist_compiled_object` (`compiler/src/pipeline/native_project/compiler.rs:182`)
persists each compiled object at `<cache_dir>/objects/<16-hex-hash>.o`, where
`cache_dir` (`compiler/src/pipeline/native_project/mod.rs`, `cache_dir()`) is
built by joining several content-hash segments onto the caller-supplied
`--cache-dir`:

```
<cache-dir>/objects/<16-hex>.o
```

`scripts/bootstrap/bootstrap-phase-verification.shs` passes a `--cache-dir`
already nested under the verification work root and keyed by two 64-hex
digests (`$snapshot_sha`, `$runtime_cache_identity`):

```
<work_root>/cache/compiler-tools/<phase>/<64-hex>/<64-hex>/full-cli
```

Concatenated with `objects/<16-hex>.o`, the final object path under
`D:\wk-bootstrap-20260924\...` measured well over 300 characters — past the
Windows 260-character `MAX_PATH` limit.

**Which call actually hits the limit, precisely.** Rust's `std::fs` on
Windows does *not* generally suffer from `MAX_PATH`: every `std::fs` entry
point routes through `sys::path::windows::maybe_verbatim` /
`get_long_path` (`library/std/src/sys/path/windows.rs`), which calls
`GetFullPathNameW` and transparently prepends the `\\?\` verbatim prefix
whenever the absolute path is long enough. That is why the two `std::fs`
calls surrounding this bug — `create_dir_all(&objects_dir)`
(`native_project/mod.rs`) and `NamedTempFile::new_in(parent)` /
`OpenOptions::open` (used internally by `tempfile::create`) — both succeed
even on a long path, so the object cache directory and the temp file inside
it are created fine; only the final rename step fails.

The failing call is `NamedTempFile::persist(cache_path)`
(`compiler.rs:188`). The `tempfile` crate's **Windows** implementation of
`persist` (`tempfile-3.24.0/src/file/imp/windows.rs:92-119`) does not go
through `std::fs` at all: it UTF-16-encodes both paths itself
(`s.as_os_str().encode_wide()`) and calls the raw Win32 APIs
`SetFileAttributesW` / `MoveFileExW` directly via `windows_sys` — bypassing
`maybe_verbatim` entirely. Those raw calls enforce the legacy `MAX_PATH`
limit on whatever path they are handed, which is exactly what silently
truncated "the directory exists, the temp file was created and written, but
the final rename fails" into a plain `ERROR_PATH_NOT_FOUND` (os error 3).

Confirmed by direct reproduction (`persist_compiled_object` copied verbatim
into a throwaway `tempfile = "3.24.0"` crate, given the same
`compiler-tools/<phase>/<64-hex>/<64-hex>/full-cli/objects/<16-hex>.o` shape
at 308 characters under this session's own scratch directory — never under
the live bootstrap worktree):

```
persist_compiled_object(&cache_path, b"..."):
  FAILED: persist cache object: The system cannot find the path specified. (os error 3)
```

— byte-identical to the real log line. Both parent directories existed
(`create_dir_all` had already run and the temp file itself was created and
written successfully; only `.persist()` failed), ruling out a missing-parent-
directory cause. Applying `win_long_path()` to the same `cache_path` before
calling the identical `persist_compiled_object` made it succeed, with a
correct cache-hit re-read afterward.

(This reproduces on **any** Windows host, including ones with
`HKLM\SYSTEM\CurrentControlSet\Control\FileSystem\LongPathsEnabled=1` set —
this dev host has that key set to `1`, and the failure still reproduces
exactly, because `tempfile`'s Windows `persist()` bypasses the mechanism
that registry key relies on (`std::fs`'s own `maybe_verbatim`) entirely. An
earlier version of this note assumed `LongPathsEnabled` would mask the bug
on this host and that the "before" case could not be reproduced live here;
that assumption was wrong — see Verification below.)

## Fix

`compiler/src/pipeline/native_project/mod.rs` adds `win_long_path()`, which
rewrites an absolute path to Windows' extended-length ("verbatim") form
(`\\?\C:\...`, or `\\?\UNC\server\share\...`), lifting `MAX_PATH` for every
Win32 file API built on it. It is applied once, in `cache_base_dir()` —
the single root all cache paths (`objects/`, per-module cache files, the
incremental manifest, and the object staging tempdir) are derived from —
so no other call site needs to change.

A verbatim path is **not** normalized by Win32: a forward slash inside it is
a literal (invalid) character, not a separator, and the whole path is
rejected (`ERROR_INVALID_NAME`) instead of being coped with. This matters
here because this crate's own default cache base,
`project_root.join(".simple/native_cache")`, embeds a literal `/` inside the
joined component (`PathBuf::join` does not rewrite separators already
present in the pushed string), and a shell-script-supplied `--cache-dir`
commonly arrives forward-slash-spelled too. `win_long_path()` normalizes all
`/` to `\` before deciding whether to prefix, and before building the
verbatim string. This was caught by direct experimentation while validating
the fix (an earlier version without the normalization step produced a
verbatim path Windows rejected with `ERROR_INVALID_NAME`, a strictly worse
regression than the original bug) — see the regression test
`normalizes_embedded_forward_slashes_before_prefixing` in
`compiler/src/pipeline/native_project/mod.rs`.

## Tests

`compiler/src/pipeline/native_project/mod.rs::win_long_path_tests` (Rust unit
tests, `cargo test --release -p simple-compiler --lib win_long_path`):

- `prefixes_a_long_absolute_drive_path`
- `is_idempotent_on_an_already_verbatim_path`
- `prefixes_unc_paths_with_the_verbatim_unc_form`
- `leaves_a_relative_path_untouched`
- `normalizes_embedded_forward_slashes_before_prefixing` (generalization spec:
  reproduces this crate's own default cache-base join, not just the reported
  `--cache-dir` shape)
- `is_a_no_op_off_windows` (non-Windows target)

All 5 Windows-gated tests pass on `x86_64-pc-windows-msvc`
(`cargo test --release -p simple-compiler --lib win_long_path_tests`, 2026-09-24).

## Verification

1. **Which binary emits the message.** `grep -rn "cache write skipped\|persist
   cache object"` across `src/compiler_rust`, every `src/**/*.spl`, and
   `src/runtime` finds the format strings in exactly one place:
   `compiler/src/pipeline/native_project/compiler.rs:192,202`. No `.spl` file
   and no C runtime file contains this text, so whatever binary
   `bootstrap-phase-verification.shs` calls `compiler.snapshot` must be built
   from this Rust crate — the pure-Simple stage-2 compiler (which would call
   `rt_*` C runtime externs, not this code) is not a candidate; that theory is
   ruled out by the grep, not by assumption.
2. **Exact failing operation, exact failing path shape, parent-dir existence.**
   Reproduced directly (see Root cause above) by calling the real
   `persist_compiled_object` function (copied verbatim, not reimplemented)
   against a path built to the exact same shape and length (308 chars) as the
   real failure, confirming: the parent directory exists and the temp file is
   created and written successfully; only the final `tempfile::persist()`
   rename fails, with byte-identical error text to the log
   (`persist cache object: The system cannot find the path specified. (os
   error 3)`).
3. **Fix verified to close it.** The same reproduction, with `win_long_path()`
   applied to the path before calling `persist_compiled_object`, succeeds and
   the object is correctly re-readable afterward (cache-hit simulation).
4. **Unit tests** (`win_long_path_tests` in `mod.rs`, `cargo test --release -p
   simple-compiler --lib win_long_path`): `prefixes_a_long_absolute_drive_path`,
   `is_idempotent_on_an_already_verbatim_path`,
   `prefixes_unc_paths_with_the_verbatim_unc_form`,
   `leaves_a_relative_path_untouched`,
   `normalizes_embedded_forward_slashes_before_prefixing` (generalization spec:
   reproduces this crate's own default cache-base join, not just the reported
   `--cache-dir` shape), `is_a_no_op_off_windows` (non-Windows target). All 5
   Windows-gated tests pass.
5. `cargo check --release --bin simple` and `cargo build --release --bin
   simple` both pass cleanly with the change.

**A real end-to-end `native-build` of a multi-file user fixture through this
seed's CLI was attempted but not completed**, for a reason unrelated to this
fix: `native-build`'s own admission path
(`src/app/cli/native_build_main.spl` -> `compiler_inventory_refresh_v1` ->
interpreted `.spl`) requires either a pre-admitted SCV source inventory or a
working `rt_fs_read_text` interpreter extern that this particular seed build
does not have backed (a separate, already-tracked interpreter-extern-registry
gap — see `.claude/rules/vcs.md` § "interpreter-extern registry gap
ratchet"), and forcing it further (`SIMPLE_SCV_FREEZE_FALLBACK=1`) reached an
unrelated worker crash (`semantic: variable 'BorrowChecker' not found`) deep
in unrelated bootstrap-worker plumbing. Item 2/3 above (the exact function,
exact path shape, exact error text, before/after) is the direct proof for
this specific defect and does not depend on that unrelated admission gate.
