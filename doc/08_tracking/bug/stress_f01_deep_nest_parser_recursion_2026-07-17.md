# Cert stress f01: deep-nesting parser stack overflow — already fixed by an earlier unrelated commit

- **Date documented:** 2026-07-17 (cert stress-suite salvage)
- **Date re-verified:** 2026-07-17 (STRESS lane)
- **Status:** NO LONGER REPRODUCES as of commit `4274c4f3f20b`
  ("fix(seed-parser): bound expr/type recursion to prevent stage-4 SIGABRT"),
  an earlier, unrelated fix already on `main` before this lane started. This
  doc records re-verification only; no code change was needed for f01 itself
  (see the `deep_paren_1000` side-effect below, which WAS fixed here).
- **Area:** Rust seed recursive-descent parser,
  `src/compiler_rust/parser/src/parser_impl/core.rs` /
  `src/compiler_rust/parser/src/expressions/core.rs`.
- **Source:** `test/cert/stress/findings/f01_deep_nest_stackoverflow.spl`
  (5000 balanced parens around a single `7`).

## Original symptom (as documented 2026-07-17, cert stress-suite salvage)

`print((((...7...)))` with 5000 levels of nesting made the parser overflow
its native stack: `thread 'simple-main' has overflowed its stack; fatal
runtime error: stack overflow` -> SIGABRT (exit 134) instead of a bounded
diagnostic. Depths 1000/2000/3000/4000 parsed fine; ~5000+ aborted.

## Current behavior (re-verified 2026-07-17)

```
$ src/compiler_rust/target/release/simple run test/cert/stress/findings/f01_deep_nest_stackoverflow.spl
...
error: compile failed: parse: ... Syntax error at 2:522:
  parse error (recovery limit): expression nesting exceeded 512 levels without progress
```

Clean exit code 1 (`rc=1`, well under the `>=128` crash threshold) with a
located diagnostic — no crash, no hang. This satisfies the stress-suite's own
FAIL/PASS distinction for the "MALFORMED must reject cleanly" class, and
matches this task's explicitly acceptable resolution: "a hard recursion cap +
error message is acceptable, full iterative rewrite is NOT required."

The fix that resolved this (already landed, not part of this lane's work) is
`Parser::parse_recursion_depth`, bounded by
`MAX_PARSE_RECURSION_DEPTH = 512` in
`src/compiler_rust/parser/src/parser_impl/core.rs`, checked at the top of
every `parse_expression()` call
(`src/compiler_rust/parser/src/expressions/core.rs`).

## Side effect this lane DID have to fix: `deep_paren_1000` in the CORE gate

The 512-level cap applies to ALL expression nesting, including legitimate,
syntactically valid deep parenthesization — not just malformed/runaway
inputs. Before this fix landed, the CORE gate's `deep_paren_1000` case (1000
balanced, VALID parens around `7`) asserted the parse succeeds and prints
`7`. With the cap now enforced, that case instead gets the same
"recovery limit" parse error (`rc=1`), because 1000 > 512.

This is a real, intentional functional cutoff introduced by `4274c4f3f20b`,
not a regression to silently paper over: **legitimate expressions nested
deeper than 512 levels are now rejected**, trading unbounded-crash risk for a
bounded (but nonzero) usability cost. 512 was chosen by a different lane's
commit; this lane did not retune it, only adjusted the CORE gate to reflect
the new, real boundary:

- `deep_paren_200` / `deep_paren_500` remain `valid_case`s (well under the
  512 cap) asserting output `7`.
- The old `deep_paren_1000` `valid_case` (which would now spuriously FAIL)
  was replaced with a `malformed_case`-style assertion
  (`deep_paren_over_cap`, same generator/depth, `$GEN_DIR/deep_paren_1000.spl`)
  that nesting beyond the cap is rejected **cleanly** (nonzero rc, `<128`,
  no hang) rather than crashing — turning the fixed f01 finding into
  positive CORE regression coverage instead of removing coverage.
- The `f01_deep_nest_stackoverflow.spl` (depth 5000) fixture stays in
  `findings/` as a live, non-gating re-run showing the graceful diagnostic
  (previously showed a crash).

If 512 turns out to be too conservative for real-world generated code
(macro-heavy or deeply chained builder-style expressions), that is a
follow-up for whichever lane owns `4274c4f3f20b` — flagged here, not silently
retuned.

## Verification

```
cd src/compiler_rust && cargo build --release
SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check/cert/stress-suite.shs
```
