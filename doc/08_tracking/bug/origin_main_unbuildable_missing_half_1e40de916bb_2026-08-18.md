# origin/main unbuildable — the missing half exists locally at `1e40de916bb` (unpushed)

**Date:** 2026-08-18
**Status:** NO SOURCE REPAIR MADE — do not revert; land the existing commit.

## Symptom
`cargo check --release --bin simple` in `src/compiler_rust` fails on `origin/main` (tip `e9e22a1230f`) with two errors:

1. **E0432** `compiler/src/interpreter_call/core/function_exec.rs:10` — imports
   `module_globals_generation` from `crate::interpreter`; no such item exists in the
   `origin/main` tree (`git grep -c "fn module_globals_generation" origin/main -- .../interpreter_state.rs` → exit 1).
2. **E0599** `compiler/src/interpreter_sffi.rs:125` — `Arc::new(f.as_ref().clone())`;
   `FunctionDef` does not implement `AsRef`.

## Investigation — the other half is NOT missing, only unpushed
Both defects are the *first* half of a change whose *second* half is already committed
in this worktree but is not an ancestor of `origin/main`
(`git merge-base --is-ancestor origin/main HEAD` → false):

- **`1e40de916bb` — "fix(seed): commit module-globals generation tracking and its two dependent fixes"**
  - `interpreter_state.rs` (+95): defines `pub(crate) fn module_globals_generation() -> u64`
    (line 43), `bump_module_globals_generation()` (47), and the bump call site (87).
  - `interpreter/mod.rs` (+1, line 73): re-exports `module_globals_generation`.
  - `interpreter_sffi.rs` (-1/+1): reverts `f.as_ref().clone()` → `f.clone()`.
  - `module_evaluator/evaluation_helpers.rs` (+20).

Introducing commits: `module_globals_generation` *uses* landed with the
`function_exec.rs` changes already on origin; the `as_ref().clone()` form was
introduced by `69f540a7f88` ("fix(native-build,linker): refuse fabricated weak stubs
for unimplemented externs") and corrected by `1e40de916bb`.

## Verdict — recommendation
**Do not revert either site.** Reverting would delete a live feature (module-globals
generation tracking) whose consumers are already on origin at
`function_exec.rs:115` and `:195`. The correct repair is for the owning session to
push `1e40de916bb`. Collateral check confirms this: `module_globals_generation` has
7 references in-tree (definition, bump helper, re-export, import, 2 call sites), so a
"drop the dead import" revert would strand both call sites and require deleting the
feature.

## Verification (working tree = origin/main + `1e40de916bb` and successors)
```
CARGO_TARGET_DIR=/mnt/data/cargo-mainrepair cargo check --release --bin simple
warning: `simple-compiler` (lib) generated 3 warnings
    Finished `release` profile [optimized] target(s) in 1m 08s
```
Exit 0. No source file was modified by this investigation.

## Guard gap
`scripts/check/check-seed-builds-push.shs` fast-paths to PASS when the outgoing range
touches nothing under `src/compiler_rust/` or `src/runtime/`. `origin/main`'s tip
commits are docs/salvage-only (`e9e22a1230f docs(tracking): ...`), so every push over the
broken tree reported PASS without compiling anything. The guard validates a *range*, not
the resulting *tree* — same class of gap that `check-c-runtime-compiles-push.shs` closed
for the C runtime by checking a TREE. Proposal: make the seed-build guard tree-scoped, or
at minimum drop the fast path whenever the base tip is not already known-green.
