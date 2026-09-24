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
Windows 260-character `MAX_PATH` limit. `tempfile::NamedTempFile::persist`
(used by `persist_compiled_object`) calls the plain (non-verbatim) Win32
rename/create APIs, which reject any path over that limit with
`ERROR_PATH_NOT_FOUND` (os error 3) rather than a length-specific error,
which is what "cannot find the path specified" against an existing directory
actually meant here.

(Whether a given Windows host also enforces this depends on the
`HKLM\SYSTEM\CurrentControlSet\Control\FileSystem\LongPathsEnabled` policy;
disabled hosts hit the limit unconditionally on ordinary paths, which is the
environment this bug report came from.)

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

## Verification note

This dev host has `LongPathsEnabled=1`, under which even the *unpatched*
raw path already round-trips (confirmed empirically), so the literal
"before" failure could not be reproduced live on this machine. The fix was
instead verified by: (1) unit tests asserting `win_long_path` produces a
well-formed, all-backslash verbatim path for both the reported `--cache-dir`
shape and this crate's own default (mixed-separator) shape; (2) a standalone
Rust program exercising the exact real path-construction shape
(`compiler-tools/<phase>/<64-hex>/<64-hex>/full-cli/.../objects/<16-hex>.o`)
and confirming write + read round-trip through the fixed form; (3)
`cargo check --release --bin simple` and `cargo build --release --bin simple`
both pass cleanly with the change.
