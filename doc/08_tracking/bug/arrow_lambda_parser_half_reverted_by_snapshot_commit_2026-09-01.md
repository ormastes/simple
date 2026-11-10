# Arrow-lambda parser work partially reverted by a "snapshot" commit

Status: OPEN — reported, NOT fixed here (out of scope of the duplicate-symbol fix).
Date: 2026-09-01

## Symptom

`cargo test --release` in `src/compiler_rust`: `simple-parser` fails 1 test,
`parser/tests/control_flow.rs:451
ts_arrow_detection_rule_was_retired_when_the_arrow_lambda_landed`.

It is tempting to read this as a stale expectation. It is not. It is an
INVERTED GUARD doing exactly the job its own comment says it exists for.

## What actually happened

`9e548aad80a fix(parser): D1 arrow lambda in BOTH parsers, ...` (a real
ancestor of `origin/main`) landed two halves together:

1. Parenthesised arrow lambda `(x) => e` / `(x, y) => e` as a supported
   production in the seed parser (`expressions/helpers.rs`,
   `expressions/primary/collections.rs`, `parser_helpers.rs`) and in the
   Simple frontend (`10.frontend/core/_ParserPrimary/primary_expr.spl`).
2. Deletion of the now-false-positive `CommonMistake::TsArrowFunction`
   detection rule in `parser/src/error_recovery.rs`, plus the inverted test
   above pinning that deletion.

On `origin/main` today, half 2 is REVERTED and half 1 is partly GONE:

- `parser/src/error_recovery.rs:502-503` again returns
  `Some(CommonMistake::TsArrowFunction)` for `) =>`.
- `/usr/bin/grep -c arrow_lambda src/compiler_rust/parser/src/expressions/helpers.rs`
  returns **0** — the helper `try_arrow_lambda_from_paren_list` that 9e548aad80a
  added exists nowhere in `parser/src/`.

`git log -S 'return Some(CommonMistake::TsArrowFunction);' -- <that file>`
names the reverting commit: **`4edef8fab8e feat: snapshot current development
state`** — a whole-working-copy snapshot, precisely the failure mode
`.claude/rules/vcs.md` § "Sync must never clobber" documents. The test survived
only because it lives in a different file the snapshot did not rewind.

## Why this must NOT be "fixed" by deleting error_recovery.rs:502-503

Deleting the rule is correct ONLY if the arrow lambda parses. It does not on
main any more — half 1 is missing. Deleting the rule alone would turn a green
test into a silent loss of a legitimate diagnostic. The repair is to restore
9e548aad80a's parser half, then the detection deletion, together.

## Repair sketch

    git show 9e548aad80a -- src/compiler_rust/parser/src/ \
        src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl

Re-apply, diffing BOTH directions against main first (main may have moved
forward on these files for unrelated reasons — see
`.claude/rules/vcs.md` § "Rebasing onto a parallel session's resolution").

## Bearing on the seed redeploy

A freshly built seed "fixes a real parser gap the deployed binary lacks". If
that gap is the arrow lambda, this record is why main lost it.


---

## 2026-11-10 (p3-compiler lane, rows 1-8, Windows worktree, seed-smoke) — SUPERSEDED ON release/1.0.0

Lane: `work/p3-compiler-20261110` on `origin/release/1.0.0` (base `dfc7da8523f4`).
Runtime: worktree Rust seed `bin/simple.exe` (built 2026-11-10). Seed-smoke only.

**Disposition: SUPERSEDED.** Both halves of `9e548aad80a` are restored on base via the
snapshot-recovery commit `5e937a7116ce fix(restore): recover rust seed code lost in stale
snapshot 4edef8fab8`:

- Seed parser: `try_arrow_lambda_from_paren_list` exists
  (`parser/src/expressions/primary/collections.rs:132,139,161`) and handles `() => e`,
  `(x) => e`, `(x, y) => e`.
- The `) =>` `CommonMistake::TsArrowFunction` detection rule is retired
  (`parser/src/error_recovery.rs:538-549` documents the removal), and the pinned guard test
  was inverted, not deleted (`parser/tests/control_flow.rs:495` now asserts
  `detect_common_mistake(FatArrow, RParen) == None`).
- Simple frontend: the D1 productions are present
  (`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:707-754`, zero/multi/single
  parameter forms).

Seed-smoke: `bin/simple.exe run` on a fixture using all three forms printed the correct
`6`, `34`, `42` (typed higher-order application of `(x) => x + 1`, `(x, y) => x*10+y`,
`() => 42`). The frontend arrow-lambda scenarios in
`test/01_unit/compiler/frontend/parser_contextual_new_scope_spec.spl` pass under the seed
("uses the supported parenthesized arrow parameter scope", "binds existing
multi-parameter arrow names before the body"). That spec still has 2 failures in
UNRELATED scenarios ("admits the supported typed var without an explicit initializer",
"blocks opaque imported shadow authority ...") — pre-existing on the release base, not
this bug. The Rust `cargo test` half of the guard remains the seed lane's to execute.
