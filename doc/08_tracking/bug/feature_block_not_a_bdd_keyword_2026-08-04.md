# `feature "..."` is not a BDD block keyword — 10 spec files are dead entry points, 300 `it` blocks never run

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Found:** 2026-08-04

## Symptom

Any spec whose top-level grouping block is `feature "..."` instead of
`describe "..."` executes nothing and reports one synthetic failure.

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/system/compiler/graph_utils_spec.spl
error[E1002]: function `feature` not found
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Expected: the 6 `it` blocks inside the `feature` group run.
Actual: `feature` resolves as an ordinary function call, is not found, and the
whole file dies before a single example is registered — so the assertions
inside have never executed even once.

Affected files and the number of `it` blocks each one hides (count of
`^\s+it "` per file):

| file | hidden `it` blocks |
|------|--------------------|
| `test/system/compiler/mir_types_spec.spl` | 44 |
| `test/03_system/compiler/mir_types_spec.spl` | 44 |
| `test/system/math/tensor_broadcast_spec.spl` | 39 |
| `test/03_system/stdlib/math/tensor_broadcast_spec.spl` | 39 |
| `test/01_unit/lib/std/parser/error_recovery_spec.spl` | 42 |
| `test/unit/lib/std/parser/error_recovery_spec.spl` | 42 |
| `test/system/compiler/symbol_hash_spec.spl` | 19 |
| `test/03_system/compiler/symbol_hash_spec.spl` | 19 |
| `test/system/compiler/graph_utils_spec.spl` | 6 |
| `test/03_system/compiler/graph_utils_spec.spl` | 6 |

300 `it` blocks across 10 files (5 unique specs, each duplicated between the
`test/<tier>/` and `test/0N_<tier>/` trees). These are dead entry points in the
same sense as `dead_entry_point_specs_336_assertions_never_ran` — the tracker
counts the file as "1 failed", which understates it by two orders of magnitude.

## Root cause

The BDD grouping keywords are hard-coded to exactly `describe` and `context` in
two places in the Rust seed, which is what `bin/simple` currently is:

- `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:510`
  — `match name { "describe" | "context" => { ... } }` (interpreter lane)
- `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:2634`
  — `match name { "describe" | "context" => { ... } }` (HIR/JIT lane)

`feature` matches neither arm, so the call falls through to ordinary function
resolution and raises `E1002`. Note `bdd.rs:553` then branches on
`name == "describe"` to decide top-level vs. nested grouping, so a new keyword
must also state which side of that it lands on (`feature` is top-level, i.e.
it should behave as `describe`).

The lint side already knows about only the two keywords:
`src/compiler_rust/compiler/src/lint/checker_spipe.rs:329`
`const BDD_KEYWORDS: &[&str] = &["describe", "context", "it ", ...]`.

The five specs all `use std.spipe.*`, so they were written against a SPipe
manual-style vocabulary in which `feature` is the outer grouping construct.
Whether `feature` should be added as a `describe` alias, or the specs should be
migrated to `describe`, is a SPipe DSL decision — but one of the two must
happen, because today the files are silently inert.

## Why not fixed now

The fix is seed-side Rust (`bdd.rs` + `stmt_lowering.rs` + the lint keyword
list), and the deployed `bin/simple` **is** that seed, so nothing takes effect
without a `cargo build --release` and a redeploy of
`bin/release/x86_64-unknown-linux-gnu/simple`. Rebuilding and swapping the
shared `bin/simple` while other sessions are mid-suite would invalidate their
runs, so it was not attempted from this lane. It is a small change — add
`"feature"` to both match arms, treat it as top-level like `describe`, and add
it to `BDD_KEYWORDS` — but it needs a lane that owns the seed rebuild, plus a
SPipe-owner decision on whether `feature` is blessed vocabulary or the specs
should be migrated instead.
