# Seed interpreter `rt_file_canonicalize` / `rt_path_absolute` leak the Windows `\\?\` verbatim prefix

- **Filed:** 2026-09-26
- **Status:** FIXED 2026-09-26 in source (see "Fix"); the frozen stage-2 authority
  seed used by the delegated bootstrap lane still carries the old behaviour until
  the seed is rebuilt and re-admitted.
- **Area:** Rust seed interpreter externs —
  `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`
  (`rt_file_canonicalize`; `rt_path_absolute` delegates to it)
- **Host:** Windows 11, x86_64-pc-windows-msvc

## Symptom

Under the seed interpreter, canonicalizing an existing path returns a Win32
*verbatim* path, while a path that cannot be canonicalized (missing, or a link
Windows cannot follow) falls back to a plain `cwd.join(path)`. The two forms
never compare equal, so any identity key built from `rt_path_absolute`
(e.g. `_driver_physical_source_key` in
`src/compiler/80.driver/driver_source_loading.spl`) splits one physical file
into two keys depending on which branch produced it.

Probe (seed `run` of a 10-line `.spl`, during the bootstrap46 triage):

```
abs_real=\\?\D:\tmp\simple-triage-symlink-probe\real\shared.spl
abs_link=D:/tmp/simple-triage-symlink-probe/shared_via_link.spl
```

## Root cause

`fs::canonicalize` on Windows returns `\\?\C:\...` (or `\\?\UNC\srv\share\...`).
The native runtime's `rt_path_absolute`
(`src/compiler_rust/runtime/src/value/sffi/file_io/path.rs`) strips that prefix
with `strip_verbatim_prefix`; the interpreter's `rt_file_canonicalize` returned
`canonical.to_string_lossy()` unchanged. The interpreter and native lanes
therefore disagreed on the same input.

## Fix

`rt_file_canonicalize` now passes the canonical path through a local
`strip_verbatim_prefix` that mirrors the runtime helper (`\\?\C:\x` -> `C:\x`,
`\\?\UNC\srv\share` -> `\\srv\share`; no-op off Windows). Regression test
`interpreter_extern::file_io::canonicalize_tests::canonicalize_returns_plain_absolute_path`:

- without the fix: `FAILED — verbatim prefix leaked: \\?\C:\Users\...\probe.spl`
- with the fix: `ok`

```
cargo test -p simple-compiler --lib canonicalize_returns_plain_absolute_path
```

Perf/mem: one prefix comparison plus one `String` copy of the path per
canonicalize call on Windows; nothing off Windows.

## Not in scope

The cwd-join fallback still does not normalize separators or resolve `..`;
it only differs from the canonical branch for paths that do not exist.
