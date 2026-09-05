# `is_dir` returns FALSE for every path, repo root included

- **Filed:** 2026-09-02 (original report `b94c58f06dc`)
- **Status:** FIXED (`src/lib/**` only — takes effect immediately, no build)
- **Host:** Windows 11, `bin/simple.exe` 16,347,136 bytes, md5 `d52d770724a9f8797e98ac7819709ab9`
  (announces itself as a bootstrap seed). POSIX **not** testable on this host.

## Symptom

Under the tree-walk interpreter (which `bin/simple test` hard-defaults to),
`is_dir` returned **false for every path**, the repository root included, while
`dir_walk` on the identical string returned 59 entries. Every `is_dir`-guarded
branch in every tool was therefore a latent no-op — the same failure class as
doc-coverage discovering 0 of 10,872 files while reporting success.

## Reproduction matrix (measured)

`SIMPLE_ENGINE_RECEIPT` **does not exist** in the seed source
(`grep -rn SIMPLE_ENGINE_RECEIPT src/compiler_rust --include=*.rs` → 0 hits; it
appears only inside prebuilt `target/**` blobs). No receipt line was emitted on
any run, so the engine is identified by the entry point instead: `run` on a
`fn main()` file = Cranelift JIT; `test` on a `*_spec.spl` = interpreter.

| path form | JIT (`run`) before | interpreter (`test`) before | both after |
|---|---|---|---|
| repo root, forward slashes | true | **false** | true |
| `.` | true | **false** | true |
| `src` (relative) | true | **false** | true |
| trailing `/` | true | **false** | true |
| genuine backslash separators | true | **false** | true |
| known file (`CLAUDE.md`) | false | false | false |
| nonexistent | false | false | false |
| `dir_walk` on the same dir | 59 | 59 | 59 |

The originally-reported "backslash fails even under JIT" is a **different
defect**: the Simple lexer DROPS `\` in a string literal — `"C:\Users\ormas"`
lexes as `C:Usersormas`, length 21 not 25 (measured). Feeding a real backslash
recovered at runtime from `dir_walk_native` (which joins with the platform
separator) shows `is_dir` answering correctly in both engines. Recorded as
`doc/08_tracking/bug/lexer_drops_backslash_escape_in_string_literal_2026-09-02.md`.

## Root cause

`is_dir` was implemented by **shelling out**, at two independent sites:

- `src/lib/nogc_sync_mut/io/dir_ops.spl:78` — `_dir_shell_bool("test -d '{path}'")`
- `src/lib/nogc_sync_mut/io_runtime.spl:495` — `shell_bool("test -d '{path}'")`
  (re-exported by `src/lib/io_runtime.spl:12`)

Both route to `process_run("/bin/sh", ["-c", ...])`. Measured directly: under
the interpreter `process_run` returns the **-1 execution-failure sentinel for
every command** — `echo hi`, `exit 0`, `find`, `test -d` alike. So the predicate
was universally false.

`dir_walk` survived only because the interpreter **substitutes the native
`rt_dir_walk` extern** for the Simple-level function: under `test`, `dir_walk`
returned byte-identical output to `dir_walk_native` (`…/bin\bb`, a Rust
`Path::join` result), not the `./`-prefixed forward-slash output `find` would
produce. `dir_list` likewise resolves to native `rt_dir_list`. **There is no
`rt_is_dir` symbol anywhere**, so `is_dir` alone fell through to the dead shell
body. That is the whole asymmetry.

Second finding, proven by bisecting the two edits: the interpreter resolves
`is_dir` *inside `dir_ops.spl`* to the **imported** `std.io_runtime.is_dir`
rather than the file's own definition — fixing only `io_runtime.spl` made
`dir_ops.is_dir` correct while its own body was still the broken shell form.
Both sites are therefore load-bearing and both were fixed. That shadowing is a
compiler defect in its own right and is recorded as
`doc/08_tracking/bug/interpreter_import_shadows_module_own_function_2026-09-02.md`.

## The runtime symbol used, and proof it exists

`rt_dir_exists` — not missing, not unbacked, simply never called from `is_dir`:

- impl: `src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs:297` —
  `Path::new(path_str).is_dir()`
- interpreter registry: `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1296`
- JIT/codegen spec: `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1984`
- symbol table: `src/compiler_rust/common/src/runtime_symbols.rs:2244`
- generated export: `runtime_symbol_entries.rs` → `__simple_runtime_symbol_rt_dir_exists`

It was already declared and used in `io_runtime.spl:103,554` (for `dir_exists`)
sitting six lines from the broken `is_dir`.

## Fix

Both sites now call `rt_dir_exists` under `unsafe(capabilities: [ffi])`.

## Cross-platform impact

**No separator handling is introduced anywhere.** `Path::is_dir()` follows
symlinks and tests for a directory — semantically identical to POSIX `test -d`.
Nothing splits, normalizes, or rewrites on `\`, so a backslash remains a legal
character in a POSIX filename. The change removes a `/bin/sh` dependency, which
is strictly a gain on baremetal and in sandboxes. **POSIX was not tested on this
host** (Windows only); the claim rests on `Path::is_dir` ≡ `test -d` semantics.

## Sibling predicates — same defect, status

| predicate | site | shells out? | status |
|---|---|---|---|
| `is_dir` | `io/dir_ops.spl:78`, `io_runtime.spl:495` | was `test -d` | **FIXED** |
| `is_file` | `io_runtime.spl:498` | `test -f` | **STILL BROKEN** — see below |
| `dir_list` | `io/dir_ops.spl:82` | `ls -1` | broken under JIT; interpreter substitutes native `rt_dir_list` |
| `list_dir` | `io_runtime.spl:511` | `ls` | same |
| `dir_walk` | `io/dir_ops.spl:63` | `find` | works only via native substitution; `dir_walk_native`/`rt_dir_walk` is the honest path |
| `file_exists` | `io/file_ops.spl:82` | no — `rt_file_exists` | OK |
| `dir_exists` | `io_runtime.spl:552` | no — `rt_dir_exists` | OK |
| `is_char_device` | `io_runtime.spl:507` | no — `rt_file_is_char_device` | OK (fixed 2026-08-07 for this exact reason) |

`is_file` is **deliberately left unfixed** rather than fixed wrongly. `test -f`
means *regular file, following symlinks*. The registered runtime offers only
`rt_file_exists` (`Path::exists`, any file type) and
`rt_file_is_regular_no_follow` (regular, but does NOT follow symlinks).
`rt_file_metadata` (`metadata.rs:332`) *does* compute follow-symlink
`metadata().is_file()` at line 386 — but it is **callable from nowhere**: it
appears in none of `common/src/runtime_symbols.rs`,
`compiler/src/interpreter_extern/mod.rs`, or `compiler/src/codegen/runtime_sffi.rs`
(all three greps return zero), has zero `.spl` callers, and its ABI is six raw
`*mut` out-parameters that Simple's `extern fn` surface cannot express. Any
composition of the two changes POSIX behaviour — either for symlinks-to-files or
for fifos/sockets/block devices — and POSIX currently works, so a "fix" here
would trade a Windows bug for a Unix regression. **Unblock condition:** add
`rt_file_is_regular` (follow-symlink `metadata().is_file()`) to
`src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs` and register it in
the three places listed above. That needs a seed rebuild, which other lanes
currently own.

## Specs

- `test/01_unit/lib/nogc_sync_mut/io/is_dir_repo_root_regression_spec.spl` —
  reproducing. Verified to FAIL against the pre-fix code: **4 of 5 failed**
  (only the nonexistent-path case passed, vacuously).
- `test/01_unit/lib/nogc_sync_mut/io/is_dir_path_form_generalization_spec.spl` —
  generalizing over absolute/relative/trailing-separator/native-separator/
  nonexistent forms and repeat-stability. 7 passed.

Both green post-fix. No `is_dir` call-site guard was removed.
