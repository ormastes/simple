# Interpreter class-name collision breaks test-DB persistence (2026-08-10)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Status: WORKED AROUND (renames); DIAGNOSTIC NOW LANDED; by-name resolution still OPEN

Update 2026-08-10: the duplicate-symbol warning is extended from functions to
classes/structs on BOTH interpreter paths:
- Pure-Simple: `struct_table_register` in
  `src/compiler/10.frontend/core/interpreter/eval_tables.spl` warns when a
  class name re-registers from a different `module_get_path()`, memoised per
  name; `struct_table_collisions()` is the observability hook. Proven by
  `test/01_unit/compiler/interpreter/class_name_collision_warning_spec.spl`
  (executed=2 passed=2; warning names BOTH module paths, quiet on
  same-module re-registration).
- Rust seed: `warn_duplicate_private_signatures` in
  `src/compiler_rust/compiler/src/pipeline/module_loader.rs` now also
  collects `Node::Class` by name and warns (always-on, once per
  name+owner-set) when one flattened module carries same-named classes from
  ≥2 owner modules.

Census 2026-08-10 (`/usr/bin/grep` over owned `src/**.spl`, vendor
excluded): 1,917 class/struct names are defined in more than one file;
1,160 of those have ≥2 definitions under `src/lib/` alone (co-loadable in
principle). Empirically LIVE in the heaviest lane (full compiler+stdlib
graph, post-renames): 0 — only the deliberate sabotage fixture warned.
Given ~1,900 latent names, the diagnostic is a WARNING, not an error.

## Symptom
Every `bin/simple test <dir>` run printed its `Results:` banner and then died
with `error: semantic: type mismatch: cannot convert string to int` (exit 1),
aborting the persistence block, so `doc/08_tracking/test/test_db.sdn` and
`test_result.md` were never written. This was the residual left after the
cold-start fix `ed0c361f8082` — before that fix the persistence block bailed
even earlier at "Warning: Could not load test database", which is why none of
these errors had ever been reachable.

## Root causes (a chain, each unmasked by fixing the previous)
1. **Precedence bug** in `cleanup_stale_runs`/`prune_runs`
   (`src/lib/nogc_sync_mut/database/test_extended/runs.spl:77,101` and the
   duplicated copies in `database.spl:317,345`):
   `row.get("start_time") ?? "" .to_int_or(0)` parses as
   `?? ("".to_int_or(0))`, so on a hit `start_time` stays a STRING and
   `now - start_time` faults. (`to_int_or` also does not exist on text — the
   dead operand was never executed, so it never errored.) Fixed with
   `(row.get("start_time") ?? "0").parse_int() ?? 0`.
2. **Class-name collision, interpreter-wide (the real defect):** the seed
   interpreter registers/resolves classes, methods, and field legality by
   NAME across all loaded modules. Under the test-runner lane THREE classes
   named `StringInterner` co-load (`std.database.core`, the test_runner
   mirror with fields `strings`/`reverse`, the seed's Rust copy) and multiple
   `FileLock` classes (`database/atomic.spl` with `for_file`, test_runner
   `test_db_lock.spl`, `sffi/io.spl` without). Dispatch is inconsistent per
   name: a method body from class A executes against an instance of class B
   ("class `StringInterner` has no field named `strings`"), or a method that
   exists only on the instance's true class reports "method not found"
   (`all_strings`, `db_interner_pairs`, `FileLock.for_file`). This is the
   class-level sibling of the `compiler_cross_module_private_symbol_collision`
   warning, which today only covers functions.
3. Workaround applied per that warning's own remedy — unique names:
   test_runner `StringInterner` → `TestDbStringInterner`, test_runner
   `FileLock` → `TestDbFileLock`, sffi `FileLock` → `SffiFileLock`. After the
   renames the full persistence chain (load → start_run → update →
   complete_run → cleanup_stale_runs → save) completes and `test_db.sdn` is
   created on a cold start.

## Repro of the interpreter defect (before renames)
```
use std.test_runner.test_db_compat.{load_test_db_compat}
use std.database.core.{StringInterner}
fn main():
    var it = StringInterner.empty()
    val _ = it.intern("hello")      # works
    val all = it.all_strings()      # "method not found" — only with the
                                     # test_runner import present
```
Without the `test_db_compat` import the same probe passes.

## Unblock condition
Interpreter should key classes by (module, name), or at minimum extend the
co-compiled duplicate-symbol warning to classes so collisions are loud.

## Gap analysis: why nothing caught any of this
- The persistence block was DEAD CODE for its entire life: `load_with_migration`
  had no cold-start branch, so no run ever got past the load. Every defect
  behind it (precedence bug, name collisions) was unreachable and therefore
  untestable until `ed0c361f8082`.
- The runner prints the failure AFTER the authoritative `Results:` line; every
  green-parsing habit ("Results says 120/120") reads the run as a pass. Only
  the exit code (1) disagreed.
- `test/01_unit/lib/test_runner/test_db_cold_start_spec.spl` (regression spec
  for the cold-start fix) was landed with `//` comments — a parse error — and
  without `use std.spec.*`, so it had never executed. Both fixed; it now runs
  `executed=3 passed=3` and fails 2/3 under a sabotaged cold-start branch.
