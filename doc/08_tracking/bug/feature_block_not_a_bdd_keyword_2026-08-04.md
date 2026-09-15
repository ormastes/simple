# `feature "..."` is not a BDD block keyword — 10 spec files are dead entry points, 300 `it` blocks never run

## Re-verified 2026-09-13 — STILL OPEN, blast radius has GROWN, and the fix site is now located

Binary: Rust seed `build/vt4/bootstrap/simple.exe` (sha256 `dc138d50276d…`),
Windows. The entry's own command, unchanged behaviour:

```
$ SIMPLE_BINARY=<abs>/simple.exe simple test test/system/compiler/graph_utils_spec.spl
SPEC FILE VERDICT: ... outcome=ERROR declared>=6 executed=0 passed=0 failed=0
error[E1002]: function `feature` not found
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Note `declared>=6 executed=0` — the harness can see the six examples and runs
none of them.

### Blast radius re-counted: 12 files, 307 `it` blocks (was 10 / 300)

`grep -rlE '^feature "' test --include=*_spec.spl`:

```
test/01_unit/compiler/bdd_feature_group_keyword_spec.spl
test/01_unit/lib/std/parser/error_recovery_spec.spl
test/03_system/compiler/graph_utils_spec.spl
test/03_system/compiler/mir_types_spec.spl
test/03_system/compiler/symbol_hash_spec.spl
test/03_system/stdlib/math/tensor_broadcast_spec.spl
test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl
test/system/compiler/graph_utils_spec.spl
test/system/compiler/mir_types_spec.spl
test/system/compiler/symbol_hash_spec.spl
test/system/math/tensor_broadcast_spec.spl
test/unit/lib/std/parser/error_recovery_spec.spl
```

The first of those is `bdd_feature_group_keyword_spec.spl` — a regression spec
for *this very defect*, which itself opens with `feature "..."` and therefore
cannot run: like `graph_utils_spec.spl` above it executes zero of its examples
and reports one synthetic failure. That is the honest state for an open bug's
regression spec (it is red, not falsely green), but it means the spec proves
nothing about the defect it guards until the keyword works.

### Fix site: the Rust seed only. The pure-Simple side already agrees.

- `src/compiler/10.frontend/parser/test_analyzer.spl:132` already declares
  `val GROUP_FUNCTIONS = ["describe", "context", "feature", "scenario"]` — the
  pure-Simple analyzer treats `feature` and `scenario` as group functions
  today.
- The seed hard-codes only two: `"describe" | "context"` at
  `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:631` (with
  `let is_describe = name == "describe"` at `:683`) and again at
  `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:3241`.

So this is a two-line-shaped fix in the seed, not a design question, and the
divergence is seed-vs-pure-Simple rather than a missing feature.

### Why it was NOT fixed in this pass, and why the spec-side workaround was declined

`src/compiler_rust/**` was off-limits (a bootstrap was running; editing Rust
sources aborts it). The alternative — rewriting `feature "..."` to
`describe "..."` across the 12 files — was deliberately **not** done: it would
switch 307 never-executed `it` blocks on at once, and there is no evidence about
how many of them pass. Landing an unknown quantity of new red as a side effect
of a keyword fix is worse than the current honest failure, and it would also
silently retire the `bdd_feature_group_keyword_spec.spl` regression spec.
Whoever fixes the seed should flip the spec files in the same change and triage
the resulting failures.

**Status:** OPEN
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
