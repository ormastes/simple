# origin/main unbuildable (Rust seed) — 2026-08-11

## Summary
`origin/main` was found unbuildable: `cargo build --release --bin simple` in
`src/compiler_rust` failed with unresolved-import (E0432-class) and
missing-enum-variant / no-such-method (E0599-class) errors, produced by two
independent incomplete changes that landed hours apart. Neither landing was
individually malicious or reckless — each was plausibly complete in
isolation — but the combination broke the build, and nothing caught it before
it reached `main`.

## Why nothing caught it
All five pre-push guards documented in `.claude/rules/vcs.md` at the time
(`check-no-conflict-tree-push.shs`, `check-no-conflict-markers-push.shs`,
`check-tree-size-push.shs`, `check-test-tree-divergence.shs`,
`check-no-revert-push.shs`) check **tree structure**: conflict trees, literal
conflict-marker text, overall tree size/shape, duplicate test-tree
directories, and revert patterns. **None of them compiles anything.** A tree
that is structurally clean — no conflicts, no markers, plausible size, no
reverts — can still be a tree that does not build. That is exactly the gap
this incident exposed.

## Fix
A sixth pre-push guard, `scripts/check/check-seed-builds-push.shs`, actually
invokes `cargo check --release --bin simple` against the pushed commit's
content (materialised into an isolated `git worktree`, never the shared
working copy). It is path-filtered for cost: it only runs the real check when
the outgoing range touches `src/compiler_rust/` or `src/runtime/`, otherwise
it PASSes immediately (reporting a non-vacuous file count). `cargo check` was
chosen over a full `cargo build --release` because the incident's actual
failures (E0432 unresolved import, E0599 missing variant/method) are pure
frontend errors — `check` catches them identically to `build` while skipping
codegen and linking — verified by the guard's own `--selftest`, which
`cargo check`s a fixture crate with a deliberately unresolved import and a
reference to a nonexistent enum variant and asserts both the failure and the
specific `E0432`/`unresolved import` diagnostic text, alongside a clean
sibling fixture that must pass.

Wired into `scripts/check/pre-push-conflict-tree-guard.shs` (the git
`pre-push` hook) alongside the tree/markers/size guards, and documented in
`.claude/rules/vcs.md`.

## Verdict contract
Same convention as the other five guards:
- `PASS — <n> file(s) checked, seed builds cleanly at <sha>` (or `... no
  compiler/runtime changes in range` on the fast path) — exit 0
- `FAIL — cargo check failed in <sha>: <first error line>` — exit 1
- `ERROR — nothing was checked` — exit 2 (includes 0-files/vacuous ranges and
  every signal/trap path)

## Follow-up
The two incomplete changes that caused the actual break are being repaired
separately (concurrent session, same day). This record is scoped to the
missing-gate defect and its fix, not the specific compile errors.
