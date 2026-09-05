# Windows `\?\` verbatim path prefix leaks into user-facing diagnostics (2026-08-31)

Status: OPEN (Rust seed, cosmetic but user-facing; Windows-only)

## Symptom

Every diagnostic that names a source file on Windows renders the Win32
*verbatim* (extended-length) path prefix `\?\`, and renders it Debug-escaped,
so each backslash is doubled again. Measured on `bin/simple.exe`
("Simple Language v1.0.0-RC", self-identifies as a bootstrap seed):

Parse error from `bin/simple.exe run`:

```
error: compile failed: parse: in "\\?\C:\Users\ormas\AppData\Local\Temp\hw\hello.spl": Unexpected token: expected Colon, found RBrace
```

Lint/loader warning from `bin/simple.exe test`:

```
warning: Avoid 'export use *' - exposes unnecessary interfaces
  --> \?\C:\Users\ormas\dev\simple\src\lib\nogc_async_mut\test_runner\doctest_runner.spl:1:1
```

Two separate problems are visible in the first line:

1. The `\?\` verbatim prefix is shown at all. It is an OS-internal form; no
   editor, IDE, or `file:line` jump-to-error parser resolves it.
2. The path is formatted with `{:?}` (Debug) rather than `{}` (Display), which
   escapes every backslash a second time — hence `\\?\C:\Users\...`.

The same failure also prints the path twice in two *different* forms within
three lines — once verbatim-Debug, once forward-slashed:

```
[engine-demotion] reason=jit-compile-error detail=module load error: parse: in "\\?\C:\Users\...\hello.spl": ...
[engine-demotion] reason=jit-compile-error detail=C:/Users/ormas/AppData/Local/Temp/hw/hello.spl
```

## Root cause (located, not patched)

Rust's `std::fs::canonicalize` on Windows always returns the verbatim
(`\?\`-prefixed) form. The compiler canonicalizes module paths during
resolution and then reuses the canonicalized `PathBuf` as the *display* path in
diagnostics, instead of keeping the user-supplied path for display. Call sites
that canonicalize include `compiler/src/hir/lower/type_resolver.rs:15`,
`compiler/src/parallel.rs:153,391`, `compiler/src/project.rs:278`, and
`compiler/src/module_cache.rs` (`normalize_path_key`, ~:318). The diagnostic is
threaded out through `driver/src/exec_core.rs:1109`
(`format!("module load error: {}", e)`).

## Why this was recorded and not fixed

The fix belongs in `src/compiler_rust`, and the session that found it could not
run `cargo` (explicit constraint), so any edit would have been unverifiable and
unbuildable. This repo has twice had `origin/main` land unbuildable from exactly
that pattern (see `origin_main_unbuildable_rust_seed_2026-08-11.md` and
`origin_main_unbuildable_missing_half_1e40de916bb_2026-08-18.md`), so an
unverified seed edit is worse than an open record.

## Suggested fix

Strip the verbatim prefix at the **display** boundary only, never at the
resolution boundary — cache keys and module identity must keep the canonical
form, or module dedup silently changes behavior. Guard it on `cfg(windows)`.
Also switch the affected `format!` sites from `{:?}` to `{}` on the path so the
backslashes are not double-escaped.

## Impact

Cosmetic, but it breaks click-to-open / jump-to-error in every editor that
parses `--> path:line:col`, on every Windows diagnostic. No effect on
correctness of compilation.

## Related

- `bootstrap_unrunnable_on_windows_git_bash_2026-08-24.md`
- `bootstrap_stage2_windows_link_unresolved_rt_and_dup_kernel32_2026-08-24.md`
