# Seed JIT spec entry always demoted (entry re-parse) + `use pkg.sym` unflattened on the JIT

- **Date:** 2026-11-14
- **Severity:** P3 (perf; correctness of verdicts unaffected)
- **Status:** fixed (seed + test runner opt-in directive)
- **Lane:** Opus (Fable unavailable)
- **Exposed by:** `test/01_unit/compiler_core/interpreter/stmt_for_comprehension_no_silent_iteration_cap_spec.spl`.
  This spec is correct, but it runs 3,000,004 core-interpreter iterations tree-walked
  by the seed, which takes about 40 min, over the 900 s cap. See the "Remaining" section of
  `seed_interp_global_array_index_store_cow_quadratic_2026-11-13.md`.

## Symptoms

`SIMPLE_JIT_SPEC_ENTRY=1 simple run <spec>` never ran a spec on the JIT. It printed:

```
module has 1 top-level statement(s) that the JIT entry path would silently skip
(it calls `main` only); falling back to interpreter
```

The `simple test` runner pins `SIMPLE_EXECUTION_MODE=interpret` on every lane, so no spec
could opt in at all.

## Root causes

1. **The entry re-parse ignores spec-entry synthesis** (`driver/src/exec_core.rs`).
   - `1d69d3992b1` (11-04) added `synthesize_spec_main`, which moves a spec's `describe` into a
     synthesized `main`.
   - `eeeabacc0fd` (11-05) changed the skipped-statement guard to RE-PARSE the entry file from
     disk, so that only entry statements are counted.
   - The on-disk `describe` is still a top-level call, so every spec-entry run was demoted.
   - **Fix:** `jit_entry_skipped_statements` returns 0 when `spec_entry` is set. Synthesis moved
     every non-binding, non-declaration item (a superset of what is counted) into `main`.
2. **An unbraced symbol import into a package aggregator is never flattened**
   (`compiler/src/pipeline/module_loader.rs`).
   - Example: `use std.spec.step` (10,847 specs) resolves to `std/spec/__init__.spl`, which
     only *re-exports* `step` via `export use std.nogc_sync_mut.spec.{..., step}`.
   - `should_flatten_import` keeps every `Single` import of an `__init__.spl` lazy. The JIT unit
     therefore got the import-binding marker but no `step` body, and refused with
     `unresolved external symbol 'step'`.
   - `use std.spec.{step}` and `use std.spec.*` were JIT'd fine.
   - **Fix:** a thread-local `FlattenPackageSymbolImportsScope` makes a symbol import into a
     package flatten exactly like `{sym}`. A whole-package `use pkg` stays lazy.
   - **Scope:** the JIT lane enters it only for opted-in spec entry (a `SIMPLE_JIT_SPEC_ENTRY`
     entry with module-level examples and no `main`).
   - Why not global: measured on the interpreter lane, flattening the `{step}` form costs 5 extra
     co-compiled warnings and about 2x RSS (62 MB -> 120 MB) per spec. Applied to every
     `fn main` JIT program, it would change JIT closures without parity evidence.
   - Ordinary programs with `use pkg.sym` still de-JIT as before.
3. **No per-spec opt-in in the runner.**
   - A `# @jit_spec_entry` header line (whole line) in
     `app/test_runner_new/test_runner_single.spl` (single-file lane) and
     `lib/nogc_sync_mut/test_runner/test_runner_execute.spl` (directory lane) switches that
     spec's child to `SIMPLE_EXECUTION_MODE=jit`, `SIMPLE_JIT_SPEC_ENTRY=1` and
     `SIMPLE_JIT_STRICT_ALL=1`.
   - `STRICT_ALL` makes a JIT refusal a fast named ERROR instead of a silent 40-minute
     interpreter run.
   - Other specs reset both flags to `0`.
   - Both flags are deliberately NOT in the process-facade grandchild env scrub
     (`process_ops.spl`). Under the light-daemon lane the runner is itself a scrub-marked
     descendant and spawns its spec child through that facade. Adding the flags to the scrub
     was tried: `/proc/<child>/environ` showed neither flag, and the spec silently tree-walked
     again. So the pins reach processes the spec spawns; use the directive on self-contained
     specs only.
   - Spec entry stays opt-in, not default: JIT/interpreter verdict parity is still only sampled
     (`seed_jit_spec_files_never_jit_2026-11-04.md`).

## Evidence (aarch64 DGX Spark, worktree seed, serial, MemoryMax=16G, timeout 900)

| run | before | after |
|---|---|---|
| `SIMPLE_JIT_SPEC_ENTRY=1 SIMPLE_JIT_STRICT_ALL=1 run <spec>` | rc=1 in 3.8 s: skipped-statement demotion | (fix 1 only) rc=1: `unresolved external symbol 'step'` |
| same, all fixes | — | rc=0, `executed on cranelift-jit: 4 passed, 0 failed`, ~144 s, peak RSS 15.2 GB |
| `simple test <spec>` (single-file lane) | ~40 min tree-walked (>900 s cap) | rc=0, 4/4, 136.9 s wall |
| `simple test <dir>` (directory lane), spec copy + mutant | — | real copy 4/4 OK; mutant (wrong int + bool) `executed=1 failed=1`, rc=1, so not vacuous |
| evidence file `SIMPLE_TEST_RESULT_FILE` | interp `simple-bdd-v1 1 0` | JIT `simple-bdd-v1 1 0` (identical) |

Rust regressions (each red before its fix, green after):

- `exec_core::tests::spec_entry_synthesis_leaves_no_skipped_entry_statements` (red: `left: 1, right: 0`).
- `module_loader::tests::unbraced_package_symbol_import_flattens_reexport_only_under_jit_scope`
  (red: "under the JIT scope `use pkg.sym` must flatten the re-exported body").

Neighbour set (10 specs, `simple test`, before/after): see the PR body.

## Remaining (not fixed here)

- **Peak RSS 15.2 GB for this spec**, close to a 16 GB cap. It is roughly the sum of the three
  1M fixtures' separate-process peaks (6.8 + 6.8 + 2.7 GB): the core interpreter's value arena
  is not reclaimed between `core_interpret` calls in one process. This is engine-independent
  and pre-existing. The tree-walked run would accumulate the same memory.
- **Spec entry is not the default.** Flipping it needs a wide JIT/interpreter verdict-parity
  sample first.
- **Pre-existing:** a runtime panic inside JIT'd code is caught by `run_file_with_args`'s
  `catch_unwind` and the file is re-run on the interpreter. That applies to every JIT program,
  not only spec entry.
