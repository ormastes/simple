# native-build's parser rejects a module-level `var x: T = ...` the seed accepts

**Status:** OPEN (P1 — blocks every push)
**Filed:** 2026-08-17
**Component:** pure-Simple parser (native-build lane) vs Rust seed parser
**Class:** engine divergence — the same source parses in one engine and not the other

## Symptom

`scripts/check/check-native-trailing-default-param.shs` fails, and with it the
pre-push hook, for **every** lane. The guard drives `native-build`, which dies:

```
error: compile failed: parse: in "src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl":
  Unexpected token: expected Fn, found Assign
error: native-build worker exited with code 1.
FAIL — native-build failed to compile the fixture
```

Bisected to `expr_dispatch.spl:49`:

```
var mir_lower_parent_expr_file: text = ""
var mir_lower_parent_expr_line: i64 = -1
```

A module-level `var` **with an initializer**. The declaration is pre-existing —
`git log -S` places it well before today — so this is not a new edit; it is
newly *reachable* because the guard now runs on every push.

## The divergence

The deployed `bin/simple` is the **Rust seed**, whose parser accepts this form —
which is why the whole compiler loads and runs from source every day. The
pure-Simple parser used by `native-build` does not. So the file is simultaneously
valid (seed) and invalid (native-build), and nothing surfaces the contradiction
until a native lane touches it.

## Ablation — this is NOT the `verification_semantic_coverage.spl` parse error

A separate report attributed the guard's RED to `d9dfcbf80e0` landing
`src/compiler/50.mir/verification_semantic_coverage.spl`, which genuinely does
not parse (a `|` or-pattern wrapped onto a continuation line — filed as
`parser_or_pattern_line_continuation_2026-08-17.md`, fixed in this change).

That attribution is **incomplete**. Measured both ways in the same worktree, same
binary:

| tree | guard |
|---|---|
| with the or-pattern fix applied | `rc=1` |
| with origin's unfixed file restored | `rc=1` |

The guard fails identically either way. Fixing the or-pattern is correct and
necessary, but it does **not** unblock the hook. The blocker is this row.

## Second-order finding: the guard fails silently in a fresh worktree

Run from a `git worktree add` checkout with no built `bin/simple`, the guard
exits 1 with **zero bytes of output** — `set -eu` plus a bare `test -x
bin/simple` terminates it before any diagnostic. That is how it was first
mis-diagnosed as "a broken guard" rather than "a broken file": absence of a
compiler is absence of evidence, and the script should say so
(`ERROR — nothing was checked`, exit 2) instead of exiting 1 mute.

## Fix direction

Either teach the pure-Simple parser the module-level `var … = …` form the seed
already accepts, or convert the two declarations to whatever form both parsers
accept — but the divergence itself is the defect and will recur elsewhere.

## Not verified

- Whether other module-level `var` initialisers exist in `src/compiler/**` and
  would fail the same way (only the first was bisected).
- Whether the seed's acceptance is deliberate or itself a laxity bug.
