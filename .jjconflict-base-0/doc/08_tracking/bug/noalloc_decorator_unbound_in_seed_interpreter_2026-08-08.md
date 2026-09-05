# `@noalloc` is unbound in the seed interpreter — module fails to load under `bin/simple test`

- **ID:** noalloc_decorator_unbound_in_seed_interpreter_2026-08-08
- **Status:** FIXED IN SOURCE, NOT YET DEPLOYED
- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** `"noalloc"` skip-list entry present at `interpreter_eval.rs:729`, but the fix is source-only: NOT YET DEPLOYED, awaiting a seed redeploy. `bug_db.sdn` row is `fix-implemented-verification-pending`.
- **Severity:** high (any stdlib module carrying `@noalloc` is unloadable by the spec harness)
- **Date:** 2026-08-08
- **Supersedes:** `noalloc_annotations_do_not_survive_import_false_alarm_2026-08-08.md`
  (landed as `e321ab17c69`) — that doc's conclusion "false alarm" is **wrong**;
  its measurement is right but covers only one of the two execution paths.

## Symptom

```
error: semantic: variable `noalloc` not found
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Any spec that (directly or transitively) imports
`src/lib/nogc_async_mut_noalloc/hash/mod.spl` — or any other module with an
`@noalloc` annotation — fails at **module load**, so `dropped`/`no examples
executed`, not a failing example.

## The discriminating condition — this is why two lanes disagreed

| probe | `bin/simple run` | `bin/simple test` |
|---|---|---|
| `use std.nogc_async_mut_noalloc.hash.{fnv1a_hash_i64}` (full path, no facade) | **PASS** | **FAIL** `variable noalloc not found` |
| `use std.hash.{fnv1a_hash_i64}` with re-export added to `src/lib/hash.spl` | **PASS** | **FAIL** |
| `use std.hash.{hash_combine}` (trait half only) | PASS | PASS |

**The axis is the execution path, not the import path.** The facade, the
`export use` re-export, and `src/std` being a symlink to `lib` are all
irrelevant to the failure. Lane A measured only `run` and concluded "no
defect". Lane B measured only `test` and blamed the facade re-export. Both
measurements are sound; both conclusions are wrong.

Edit-visibility was proven for both paths before any row was trusted:
- `run`: a hard `return 7731` planted in `fnv1a_hash_i64` printed `R4=7731`.
- `test`: commenting out the four `@noalloc` lines flipped the spec 0/1 -> 1/1.
Both sabotages reverted; `mod.spl` byte-identical at `726e20e6d3b14336cee8fcd775be948543e0e330`.

## Root cause

`@noalloc` is documented and semantically load-bearing in this repo
(`src/compiler/35.semantics/noalloc_checker.spl`, `effect_verifier.spl`,
the `noalloc: bool` column in `gc_boundary_check.spl`'s family manifest) but
**the string `"noalloc"` appears in no parser in either implementation** — zero
hits in `src/compiler/**/*.spl` and zero in `src/compiler_rust/**/*.rs`.
It was never wired in.

The Rust seed interpreter
(`src/compiler_rust/compiler/src/interpreter_eval.rs`, function-decorator
application) treats every `@X` on a function as a **Python-style runtime
decorator**: it calls `evaluate_expr(Identifier("X"))` against the module env
unless `X` is on a hardcoded skip-list (`extern`, `deprecated`, `gpu_kernel`,
`gpu_device`, `gpu_shared`, `hardware`, `clocked`, `generic`,
`flatten_struct_output`). `noalloc` was absent, so it was looked up as a
variable and the lookup failed — `interpreter/expr/literals.rs:361`.

Allowlist confirmed by a 3-line reproducer (`@X` + `fn zz_twice`, imported by a
1-example spec):

| annotation | result |
|---|---|
| `@inline`, `@pure`, `@unsafe`, `@hardware` | 1/1 PASS |
| `@noalloc`, `@zzbogus` | 0/1, `variable <name> not found` |

`bin/simple run` uses the JIT/native path, which never evaluates decorator
expressions — hence its blindness.

The pure-Simple parser is **not** affected: its module-level decorator branch
(`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`, kind 171)
dispatches known names and silently drops unknown ones without synthesising an
identifier expression.

## Fix

`src/compiler_rust/compiler/src/interpreter_eval.rs` — add `noalloc` to the
decorator skip-list.
`src/compiler_rust/compiler/src/lint/checker_core.rs` — add `noalloc` to
`KNOWN_DECORATORS` (list-completeness; no lint warning was observed either way,
so this half is **unverified**).

Verified with a locally rebuilt seed (`src/compiler_rust/target/release/simple`,
`bin/release/**` deliberately NOT redeployed):

```
SIMPLE_BINARY=<rebuilt> <rebuilt> test test/unit/lib/zz_ann_probe_spec.spl          -> 1/1
SIMPLE_BINARY=<rebuilt> <rebuilt> test test/unit/lib/zz_noalloc_direct_probe_spec.spl -> 1/1
SIMPLE_BINARY=<rebuilt> <rebuilt> test test/unit/lib/std_hash_facade_spec.spl        -> 5/5  (with the noalloc re-export added)
```

## Dependent work — do NOT land before a seed redeploy

`src/lib/hash.spl` and `src/lib/string.spl` are each missing an `export use` of
their shadowed `nogc_async_mut_noalloc` package:

- `hash`: `fnv1a_hash_bytes, fnv1a_hash_i64, crc32_byte, crc32_bytes`
- `string`: `bm_str_len, bm_str_eq, bm_str_starts_with, bm_str_ends_with, bm_str_find, bm_int_to_str, bm_str_to_int, bm_hex_to_int`

Both re-exports work on the rebuilt seed and both **break the tree on the
currently deployed seed** — `src/lib/nogc_sync_mut/src/map.spl` imports
`std.hash`, so a premature landing poisons Map/Dict everywhere. Land them in
the same change as, or after, a redeploy carrying the interpreter fix.

## Follow-ups filed separately

- `unknown_function_annotation_evaluated_as_runtime_identifier_2026-08-08.md` —
  the fail-open that let a never-wired annotation ship in stdlib.
- `simple_test_child_binary_ignores_invoking_binary_recurrence_2026-08-08.md` —
  `find_simple_binary()`'s `/proc/self/exe` step did not hold; a rebuilt seed
  silently delegated to the stale deployed binary.

## 2026-08-17 re-verification (lane m1_rust_interp) — FIXED IN SOURCE (deploy lag only)

Classified by CONTENT (per session CORRECTIONS #1).

`src/compiler_rust/compiler/src/interpreter_eval.rs:710-729` now lists
`"noalloc"` in the set of decorator names that are skipped rather than resolved
as runtime bindings, alongside `extern`/`deprecated`/`hardware`/`clocked`/
`generic`/`flatten_struct_output`, and additionally `alloc`, `no_alloc`,
`no_mangle`, `gpu`. The code carries an explicit back-reference to THIS doc at
:718 and restates the mechanism ("invisible via `bin/simple run` — the JIT path
never evaluates decorator expressions").

This confirms the doc's own "FIXED IN SOURCE, NOT YET DEPLOYED" status. The
residual is purely a redeploy of `bin/simple`, not a source defect.

**Status: RESOLVED in source.** Close once the seed in `bin/release/` is
rebuilt; nothing further to change in the interpreter.
