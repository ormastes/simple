# std.shell file/dir ops: existence checks return false after create operations

- **Status:** FIXED 2026-06-11
- **Found:** 2026-06-11 by the hollow-assert sweep (SPIPE006 de-hollowing) —
  one of these failures was previously HIDDEN by a bare `expect(...)` no-op;
  the other three already failed at tip on neighbouring assertions.
- **Severity:** medium — interpreter-mode failures in
  `test/01_unit/lib/std/shell/file_system_spec.spl` (4 of 9 tests red).

## Failing tests (interpreter mode) — pre-fix

| Test | Symptom |
|------|---------|
| should check if file exists | `assert_true(file.exist(path))` → false right after the spec creates the file |
| should create and remove directory | `semantic: unknown static method create on class dir` |
| should create recursive directory | `assert_true(...)` → false after recursive mkdir |
| should list directory entries | `semantic: unknown static method create on class dir` |

Write/read/append/copy/rename tests in the same spec PASS — basic file I/O
works; failures clustered on `file.exist`, `dir.create`, recursive mkdir,
and dir listing through the std.shell wrappers.

## Root cause (found 2026-06-11)

Three distinct bugs:

### 1. `file.exist` test used a stale hardcoded path
`test/01_unit/lib/std/shell/file_system_spec.spl` line 10 checked
`file.exist("simple/std_lib/test/unit/shell/file_system_spec.spl")` — a path
that has never existed in the repo. Fixed by writing a temp file first and
checking that.

### 2. `dir.create` / `dir.remove` semantic error — missing externs + strict arity
`use std.shell.{file, dir}` resolves to `src/compiler_rust/lib/std/src/shell.spl`
(searched before `src/lib/`). That file had:
- `extern fn rt_dir_create(path: text, recursive: bool) -> bool` — 2-param
- `static fn create(path: text, recursive: bool = false)` — 2-param with default

The interpreter's `constructor_overload_score` requires **exact** param count match:
`func.params.len() != values.len() → None`. So `dir.create(path)` with 1 arg
never matched the 2-param method — error "unknown static method create on class dir".

**This is a Rust seed bug** (`interpreter_method/special/objects.rs:38`
`constructor_overload_score` ignores default parameter values). NOT fixed in Rust.

Worked around in Simple source by replacing the 2-param variants with 1-param
methods that dispatch to the correct extern:
- `rt_dir_create(path)` (1-arg) and `rt_dir_create_all(path)` added
- `rt_dir_remove(path)` (1-arg) and `rt_dir_remove_all(path)` added

### 3. `create_recursive` called wrong extern
`dir.create_recursive(path)` called `rt_dir_create(path, true)` — the legacy
2-arg extern that the interpreter reads only arg[0] from (creates non-recursive).
Nested dirs never created. Fixed to call `rt_dir_create_all(path)`.

### 4. `io_runtime.spl` `dir_create` passed wrong args to extern
`pub fn dir_create(path, recursive: bool)` called `rt_dir_create(path, recursive)` but
`extern fn rt_dir_create(path: text) -> bool` is 1-arg. Fixed: route `recursive=true`
→ `rt_dir_create_all`, `recursive=false` → `rt_dir_create`.

## Files changed

- `src/compiler_rust/lib/std/src/shell.spl` — fixed extern decls and `class dir` methods
- `src/lib/nogc_sync_mut/shell/file.spl` — new: file namespace module
- `src/lib/nogc_sync_mut/shell/dir.spl` — new: dir namespace module (backup path)
- `src/lib/nogc_sync_mut/shell/mod.spl` — added file/dir namespace dict exports
- `src/lib/nogc_sync_mut/shell/__init__.spl` — export file, dir
- `src/lib/nogc_sync_mut/io_runtime.spl` — fix dir_create to route via recursive flag
- `test/01_unit/lib/std/shell/file_system_spec.spl` — fix stale path in file.exist test

## Post-fix results

- `test/01_unit/lib/std/shell/file_system_spec.spl`: **9/9 PASS** (was 5/9)
- `test/01_unit/lib/std/file/file_io_spec.spl`: **0/4 FAIL** (pre-existing, unrelated —
  fails due to `unknown extern function: rt_check_file_path`; unchanged by this fix)

## Open: Rust seed default-param arity bug

`constructor_overload_score` in `interpreter_method/special/objects.rs` treats
methods with default parameters as requiring exact arg count. Any static class method
with optional params is unreachable with fewer args than declared params.
Repro: any `class Foo` with `static fn bar(x: text, y: bool = false)` — `Foo.bar("x")`
gives "unknown static method bar on class Foo".
Fix needed in Rust seed but out of scope for this task.
