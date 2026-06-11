# std.shell file/dir ops: existence checks return false after create operations

- **Status:** open
- **Found:** 2026-06-11 by the hollow-assert sweep (SPIPE006 de-hollowing) —
  one of these failures was previously HIDDEN by a bare `expect(...)` no-op;
  the other three already failed at tip on neighbouring assertions.
- **Severity:** medium — interpreter-mode failures in
  `test/01_unit/lib/std/shell/file_system_spec.spl` (4 of 9 tests red).

## Failing tests (interpreter mode)

| Test | Symptom |
|------|---------|
| should check if file exists | `assert_true(file.exist(path))` → false right after the spec creates the file |
| should create and remove directory | fails in create/remove sequence |
| should create recursive directory | `assert_true(...)` → false after recursive mkdir |
| should list directory entries | listing after creation does not match |

Write/read/append/copy/rename tests in the same spec PASS — so basic file
I/O works; the failures cluster on `file.exist`, `dir.exist`, recursive
mkdir, and dir listing through the std.shell wrappers.

## Fix direction

Root-cause the std.shell wrappers (`file.exist`/`dir.*`) against the working
io_runtime primitives the passing tests use — likely a path-normalisation or
wrapper-dispatch gap in interpreter mode rather than missing OS support.
Do NOT skip or weaken the spec; it now asserts honestly.
