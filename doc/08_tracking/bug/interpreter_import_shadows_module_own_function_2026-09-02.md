# Interpreter resolves a module's own function to an unrequested import

- **Filed:** 2026-09-02 — isolated while fixing
  `is_dir_always_false_shell_dependency_2026-09-02.md`
- **Status:** OPEN (compiler/interpreter defect; not fixed here)
- **Host:** Windows 11, `bin/simple.exe` 16,347,136 bytes,
  md5 `d52d770724a9f8797e98ac7819709ab9`

## Symptom

`src/lib/nogc_sync_mut/io/dir_ops.spl` defines its own `fn is_dir` and imports
only `process_run`:

```
use std.io_runtime.{process_run}
```

`std.io_runtime` (via `src/lib/io_runtime.spl:12`) also exports an `is_dir`.
Under the tree-walk interpreter, a caller importing
`std.nogc_sync_mut.io.dir_ops.{is_dir}` gets **`std.io_runtime`'s** `is_dir`,
not the one defined in the file it named.

## Bisection proof

Two independent edits, four measured states, one probe printing
`is_dir(cwd())` under `bin/simple test`:

| `io_runtime.spl` `is_dir` | `dir_ops.spl` `is_dir` | observed |
|---|---|---|
| shell (`test -d`) | shell (`test -d`) | **false** |
| shell | native (`rt_dir_exists`) | **false** |
| native | shell | **true** |
| native | native | true |

Row 2 vs row 3 is decisive: changing `dir_ops.spl`'s own body did **not** change
`dir_ops.is_dir`'s behaviour, and changing `io_runtime.spl` did. The file's
definition is dead under the interpreter.

## Same mechanism, second instance

`dir_walk` in the same file is defined as a `find` shell-out, yet under the
interpreter it returns output byte-identical to `dir_walk_native`
(`…/bin\bb` — a Rust `Path::join` result), not `find`'s `./`-prefixed
forward-slash output. `dir_list` likewise returns `rt_dir_list`'s result rather
than `ls -1`'s. Substitution to a same-named native extern hid a completely
dead shell lane for both.

## Why it matters

This is a silent-wrong-answer class, not a crash. It makes a module's source
non-authoritative: a reader auditing `dir_ops.spl` sees one implementation while
another executes, and it defeats bisection (a fix applied to the correct-looking
file appears to do nothing). It is precisely why the `is_dir` outage needed the
fix applied at **two** sites, and why `dir_walk` appeared healthy while its
implementation was dead.

## Unblock / owner

Interpreter module/name resolution
(`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs` and the
extern registry in `interpreter_extern/mod.rs`). A file-local definition must
win over any imported name, and an import naming `{process_run}` must not bring
`is_dir` into scope at all. Verifying the fix needs a seed rebuild.
