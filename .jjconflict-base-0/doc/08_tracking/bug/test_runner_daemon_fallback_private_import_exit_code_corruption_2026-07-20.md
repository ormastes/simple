# `bin/simple run <spec>.spl` exits nonzero when the import graph transitively
# lazily-loads a module with its own `fn main()` — root-caused and fixed

**Date:** 2026-07-20 (root-cause lane; supersedes/resolves the prior OPEN
writeup of the same title — see "Prior investigation" below)
**Severity:** medium (does not silently false-green anything — the opposite:
a fully-green spec's file-level summary reported one extra failure it never
had)
**Status:** RESOLVED. Root cause identified with PROVEN mechanism (strace +
loader tracing + source read, not speculation) and fixed at the two exact
leak sites. Fix verified against the minimal repros and the held spec on a
binary built from this change.

## Prior investigation (context, not re-derived)

A previous lane pinned the trigger down precisely (minimal 4-line repro
importing `std.test_runner.test_runner_files.{strip_ansi}` or
`std.test_runner.doctest_runner.{extract_doctests}`, two clean negative
controls) but could not find the mechanism; two candidate causes (`[gc-warning]`
family-tier diagnostic, `export use *` parser hint) were checked against
source and proven non-fatal by construction. Full writeup: prior revision of
this doc (commits `ed53f026ec0` / `34d900e5bfc` / `862bda8ee9e`, not yet on
`main` as of this lane's fetch at `c12f965ba50a`).

## PROVEN mechanism

Traced with `strace -f -tt -e trace=%process,write` on the minimal
`doctest_runner` repro (`bin/simple run <probe>.spl`, zero ANSI bytes, one
trivial `expect(1).to_equal(1)`):

- The interpreted BDD example runs correctly and prints
  `1 example, 0 failures` to fd 1.
- **0.5ms later, on the exact same thread, with no further module-loading
  trace lines**, `Usage: native.spl <source.spl> <output> ...` is written to
  fd 1 — the literal usage-and-`return 1` body of
  `src/app/compile/native.spl:528-541`'s `fn main()`.
- `exit_group(1)` follows ~0.4s later. That `1` is `native.spl`'s `main()`
  return value, not a real test failure.

`SIMPLE_LOADER_TRACE=1` confirms `app.compile.native` *is* loaded during this
run (`[loader-trace] loaded: .../src/app/compile/native.spl (8617 exports,
14d, 31ms)`), reached transitively:
`doctest_runner.spl` → (`find_simple_binary` /
`process_run_bounded`-reachable code) → `app.io.cli_commands` →
`app.io.cli_compile` → `app/io/_CliCompile/compile_opt_and_driver.spl`
(`use lazy app.compile.native (compile_native)`) → `native.spl`. This deep,
~8600-export chain is also why the run takes ~20s even for a 1-example spec
(a separate, pre-existing perf issue — see
`doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md`).

`src/compiler_rust/compiler/src/interpreter_eval.rs:480-489` (pre-existing
comment, from an earlier partial fix for a related symptom) documents the
general shape: `evaluate_module_impl` captures `entry_main =
functions.get("main")` **after the first registration pass but before any
lazily-loaded module can merge into `functions`**, specifically so a
lazily-loaded module's own `main` cannot clobber a *real* entry `main`. But
at the end of the function (line ~1572, pre-fix):

```rust
let main_to_run = entry_main.clone().or_else(|| functions.get("main").cloned());
```

When the entry script (our BDD spec) defines **no** `main` of its own,
`entry_main` is `None`, and the fallback silently picks up whatever stray
`main` got merged into `functions` later — i.e. `native.spl`'s own
CLI-entry `main()`, called with zero args, printing its usage text and
returning `1`. That `1` becomes the whole process's exit code.

### Why `native.spl`'s `main` survived the "don't merge main" guard

Every *other* merge-into-`functions`/`global_functions` site in the
codebase already guards against exactly this:

- `register_definitions` (`interpreter_module/module_evaluator/evaluation_helpers.rs:112-116`, first pass)
- `merge_cached_module_definitions` (`module_cache.rs:306-311`, cache-hit path)
- the fresh-load merge in `load_and_merge_module` (`interpreter_module/module_loader.rs:1059-1065`)

all skip `main` with `if name != "main"`. **Two sites did not:**

1. `process_use_stmt`'s exports-unpacking loop
   (`interpreter_module/module_evaluator/evaluation_helpers.rs`, ~line 526-528
   pre-fix) — used when evaluating an *imported module's own* `use`
   statements (i.e. reached while recursively loading `compile_opt_and_driver.spl`,
   not while executing our probe's top-level statements). It unpacked
   **every** entry of the loaded module's exports dict into
   `global_functions` unconditionally, regardless of `use_stmt.target`
   (so even though the actual `use lazy app.compile.native (compile_native)`
   statement only *asked for* `compile_native`, the internal merge pulled in
   `main` too).
2. `interpreter_eval.rs`'s runtime `Node::UseStmt` handler, `ImportTarget::Glob`
   branch (~line 1325-1338 pre-fix) — same unconditional pattern, reachable
   when a literal `UseStmt` node survives pipeline flattening into the
   interpreted entry `items` list (the `use lazy` eager-in-the-seed path
   documented at `evaluation_helpers.rs:497-502`).

Feeding `native.spl`'s exports (which include `main`, since
`export_functions` in the same file, lines ~715-727, exports *all*
top-level functions by default with no `main` filter — left as-is; that
export set is legitimately cached/shared for qualified access, only the
*merge into the flat callable-by-bare-name `functions` map* is the bug)
through either unguarded site clobbers `functions["main"]`, and since our
probe's `entry_main` was `None`, the clobbered value became `main_to_run`.

## Fix

Added the same `if name != "main"` guard already used at the other three
sites, at the two sites that lacked it:

- `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
  (`process_use_stmt`, the `global_functions.insert(name.clone(), Arc::clone(def))`
  call in the exports-unpacking loop)
- `src/compiler_rust/compiler/src/interpreter_eval.rs`
  (the `ImportTarget::Glob` branch's `functions.insert(name.clone(), Arc::clone(def))` call)

Deliberately left unguarded (matches every other site's existing behavior,
and is out of scope): `FUNCTION_OVERLOADS` registration (also unconditional
at `register_definitions`, not implicated in this exit-code bug),
`export_functions`'s own exports dict (used for qualified/cached access,
not the flat bare-name dispatch table that `main_to_run` reads), and the
`ImportTarget::Group`/`Single`/`Aliased` extraction branches (already
correctly scoped to only the explicitly-requested item names).

## Verification

Built `bin/release/.../simple` (the Rust seed) from this change
(`cargo build --release -p simple-driver --bin simple`, ~1m48s incremental
against the shared target dir). Before/after, same binary build loop:

| Case | Pre-fix | Post-fix |
|---|---|---|
| `bin/simple run` on 4-line probe importing `doctest_runner.{extract_doctests}` | exit 1 | exit 0 |
| `bin/simple run` on 4-line probe importing `test_runner_files.{strip_ansi}` | exit 1 | exit 0 |
| `bin/simple run` on control probe (`nogc_sync_mut.array.{array_count}`) | exit 0 | exit 0 (unaffected) |
| `bin/simple run` on a script with its own `fn main()` | n/a | still runs its own main correctly (exit 0, "own-main-ran" printed) |
| `bin/simple test test/01_unit/app/test_runner_strip_ansi_spec.spl` | `Passed: 12` / `Failed: 1` (phantom) | `Passed: 12` / `Failed: 0` |

The held spec `test/01_unit/app/test_runner_strip_ansi_spec.spl` now reports
**12 passed / 0 failed**, matching its real `12 examples, 0 failures` BDD
summary with no phantom `+1`.

`cargo test --release -p simple-compiler --lib module` (173 tests matching
the `module` substring, covering `module_loader`/`module_cache`/
`module_evaluator` and related interpreter-module code): **173 passed, 0
failed**. Not run: the full `simple-compiler` suite (thousands of tests,
out of this lane's time budget) — rerun before landing if that matters to
the deploy gate.

## Cross-references

- `doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md`
  — same underlying deep-import-graph relint traversal, as a separate
  performance defect (~20s+ for a 1-example spec here; 550-900s+ for
  `arch_check_spec.spl`). Not fixed by this change; still open.
- `doc/08_tracking/bug/stage4_test_runner_strip_ansi_superlinear_hang_2026-07-20.md`
  — already exonerates `strip_ansi`/`parse_test_output`; unaffected by this
  fix.
