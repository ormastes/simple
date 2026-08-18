# Committed tree does not compile; only the dirty worktree does

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
