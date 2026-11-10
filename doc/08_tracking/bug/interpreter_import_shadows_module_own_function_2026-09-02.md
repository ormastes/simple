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

## Addendum 2026-11-11 — lane interp5 verdict: SUPERSEDED

Verdict: **SUPERSEDED** — the exact resolution defect no longer reproduces on
the refreshed seed. The seed-rebuild precondition this bug was waiting on has
happened (tracked `bin/simple.exe` is now the 2026-11-11 refreshed seed), and
the seed-interpreter resolution family has since been fixed:

- `10e216d19f8c9b2dd9bf8fd24544793c6ad07caa` (2026-11-09, "fix(resolve):
  ambiguous co-compiled duplicate definition is a compile error (owner decision
  6)") — touched `pipeline/module_loader.rs` plus four interpreter call-path
  sites: the caller's own definition wins, an import brings only the names it
  names, unresolved ambiguity is a compile error.
- `7a60d8bb19fa8c449d901e046929e802fbfb49a6` (2026-11-06, "fix(seed-interp):
  fn-valued locals shadow imported functions") — lexical locals win first.
- Related pure-Simple resolver tiering: `21ac6ca4ec1d` (2026-11-04, local tier
  wins over stdlib import tier).

All are ancestors of base `b364745fdbf8`.

Seed-smoke verification (2026-11-11, lane interp5, refreshed seed
`bin/simple.exe` 2026-11-11 build, `SIMPLE_LIB=src`, `SIMPLE_TIMEOUT_SECONDS=0`).
Minimal reduction of the reported shape — module Target defines its own
`fn marker() -> "LOCAL"` and imports only `{other}` from module Source, which
also exports `marker() -> "IMPORTED"`; a caller imports
`Target.{marker}`:

- Interpreter (`SIMPLE_EXECUTION_MODE=interpret`): prints
  `probe -> LOCAL` — the file-local definition wins; the unrequested same-named
  import does not enter scope.
- JIT control (`SIMPLE_EXECUTION_MODE=jit`): identical, `probe -> LOCAL`.

Scratch probe modules lived only under `src/lib/interp5_probe_*.spl` for the
run and were deleted afterwards (`git status` clean). The original second
instance (`dir_walk`/`dir_list` shell lanes) is independently moot: both files
now use the native provider by owner decision (see
`seed_directory_discovery_shell_provider_2026_10_05.md` and the comments at
`src/lib/nogc_sync_mut/io/dir_ops.spl:68-93`). No further action.
