# native-build's parser rejects a module-level `var x: T = ...` the seed accepts
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** CLOSED (outdated, 2026-11-05) — see addendum.
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


## Addendum 2026-11-05 — closed as outdated (W3b)

Stage3 `s3_fable44` builds, links and runs a fixture with module-level
`var x: i64 = -1` and `var s: text = ""`: rc=0, stdout `PASS modvar`.

## 2026-11-10 status — SUPERSEDED (P3 bootstrap lane row 45, work/p3-boot6-20261110)

Corroborates the W3b addendum. Source-verified on this lane's base
(`4343ce254922`): the pure-Simple parser now accepts the module-level
`var x: T = <expr>` form the record says it rejected —
`src/compiler/10.frontend/core/parser_decls_use.spl:454-486` parses the
annotized declaration, requires `=` for types with no safe zero (fn type,
text, Option, dynamic array) with an explicit diagnostic, synthesizes zero
defaults for scalars/fixed arrays/named types, and falls through to
`parse_expr` for the initializer. Divergence itself is closed: the seed's
lax acceptance and the native-build parser's rejection were reconciled in
the parser, which is the fix direction this record prescribes. Pins in tree:
`test/01_unit/compiler/parser/module_noinit_zero_default_spec.spl`,
`test/01_unit/compiler/parser/module_noinit_enum_class_zero_spec.spl`
(queued under seed-smoke this pass; results in
build/review/p3fix-boot6-20261110.sdn).
The two `expr_dispatch.spl` declarations named in this record still exist
and are accepted forms today. Not re-verified end-to-end by this lane: a full
native-build of a modvar fixture is a ~2-3 GB interpreted-worker run
(heavy-forbidden); W3b (2026-11-05) already holds the end-to-end rc=0.
