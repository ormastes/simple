# Committed tree does not compile; only the dirty worktree does

Status: RESOLVED 2026-08-18, commit `1e40de916bb`.

## Resolution

Root cause confirmed: `interpreter/mod.rs` already re-exported
`module_globals_generation`/`report_globals_census` on the committed tip, but
their definitions (a `GenTrackedCell` wrapper around the module-globals
thread-locals in `interpreter_state.rs`) existed only as an uncommitted edit in
the shared worktree. That same uncommitted change also required
`export_functions()` in `evaluation_helpers.rs` to take a frozen
`&Arc<HashMap<String, Value>>` instead of `&Env`, and dropped a stale
`f.as_ref().clone()` in `interpreter_sffi.rs` (the field's type changed under
the same refactor). All four edits are one coherent completion of an
already-committed change (the `interpreter/mod.rs` re-export line), not
unrelated WIP.

Committed exactly these four files, nothing else from the shared worktree's
other uncommitted diffs (`node_exec.rs`, `block_exec.rs`,
`interpreter_helpers/patterns.rs`, `expr/calls.rs`, `place.rs`,
`mir/lower/lowering_expr_method.rs`, `driver/src/exec_core.rs`, `driver/src/log.rs`
remain uncommitted and untouched — not verified as required for this fix, left
for their owning session):

- `src/compiler_rust/compiler/src/interpreter_state.rs`
- `src/compiler_rust/compiler/src/interpreter_sffi.rs`
- `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
- `src/compiler_rust/compiler/src/interpreter/mod.rs`

Proof: `git worktree add --detach <tmp> HEAD` at `1e40de916bb` (after commit),
then `cargo check --release --bin simple` in `src/compiler_rust` under a
dedicated `CARGO_TARGET_DIR` → exit code `0`, "Finished `release` profile
[optimized] target(s) in 1m 03s". Verified BEFORE committing too, by
`git apply`-ing just these four files' diff into a separate clean worktree at
the pre-fix tip and confirming the same exit-0 build, isolating that these four
files (not the rest of the shared worktree's dirty state) are what was missing.

`sh scripts/check/check-seed-builds-push.shs origin/main..HEAD` final confirmation:

```
check-seed-builds-push: selftest 4/4 fixtures correct (E0432/E0599-shape FAIL, clean PASS, target-scope gap: --bin PASS + --tests FAIL, vacuous-range contract)
check-seed-builds-push: PASS — 1699 file(s) checked, seed bin + test targets compile cleanly at HEAD (link NOT verified: cargo check does not link)
```
exit 0.

---

Status: OPEN. Filed 2026-08-18.
Precedent: `origin_main_unbuildable_rust_seed_2026-08-11.md` (same failure class).

## Evidence

Building the Rust seed from a CLEAN `git worktree` at the current committed tip
fails with 4 errors: `E0432` (unresolved import), `E0425` (not found in scope),
`E0308` (mismatched types), `E0599` (no method). The same build SUCCEEDS in the
shared working copy `/mnt/data/worktrees/simple-main`.

Difference: the shared copy carries another session's **uncommitted** changes to
`src/compiler_rust/compiler/src/interpreter/node_exec.rs`,
`interpreter/block_exec.rs`, `interpreter_helpers/patterns.rs` and others. One of
them is a `MODULE_GLOBALS` reentrant-borrow fix. Those edits are load-bearing for
compilation but exist only in a working copy.

Found incidentally while probing
`spec_runner_executes_it_bodies_twice_2026-08-18.md` (an agent needed a clean
worktree to build an instrumented seed, and could not).

## Why it matters

- Anyone cloning or checking out the committed tip cannot build the seed.
- `scripts/check/check-seed-builds-push.shs` materialises the NEW tip into an
  isolated worktree precisely to catch this — so it will (correctly) block
  pushes whose range touches `src/compiler_rust/` or `src/runtime/` until the
  missing fixes are committed.
- The green build everyone sees locally is an artifact of uncommitted state:
  the classic "works on my machine" made repo-wide.

## Wanted

The session holding those edits commits them (they are the fix, not the
breakage). Per the Fix test standard
(`doc/03_plan/infra/binary_runtime_hardening/plan.md`), the commit should carry
the clean-worktree build as its reproduce evidence: build from
`git worktree add --detach <tmp> HEAD` and show `cargo check --release --bin
simple` passing there, not just in the shared copy.
