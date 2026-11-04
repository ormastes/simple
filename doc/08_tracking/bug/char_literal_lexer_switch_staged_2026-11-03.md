# char_literal_lexer_switch_staged_2026-11-03

- **Status:** open — blocked (not fixable in this lane)
- **Priority:** P2
- **Decision:** ADR-005 § "Char literal syntax" (`doc/04_architecture/adr/ADR-005-text-index-yields-char.md`)
- **Last checked:** 2026-11-04 on `origin/release/1.0.0`

## What the switch is

After the switch, single quotes lex only as a `char` literal: exactly one
Unicode scalar or one escape. Multi-scalar `'...'` becomes a lex error that
points at `r"..."`. `'ident` with no closing quote stays a label.

## Why it cannot land yet

ADR-005 step 3: the lexer switch lands only after the stage3 self-build
passes. The frozen stage2 compiles the compiler's own lexer. If the meaning of
`'...'` changes before every compiler-source site is converted, the bootstrap
breaks.

State of the gate on 2026-11-04:

- macOS (bootstrap lane 1, `/private/tmp/lanes/stage_artifacts.txt`): the
  stage2 binary was built but **not admitted**, because the sanity check was
  refused by the memory reserve. Lane runs `s2c`/`s2d` were in flight.
  Stage 3 has not been reached.
- No platform has recorded a passing stage3 self-build on this line since the
  decision. Bootstrap is owned by the bootstrap lane, so bug-fix lanes may not
  run it.

## Prerequisites already landed

| step | artifact | state |
|---|---|---|
| migration tool (uses the real lexer) | `src/app/tools/raw_quote_migrate/{main,rewrite}.spl` (`dcab80d215d`) | landed |
| no-new-sites ratchet | `scripts/check/check-no-single-quoted-raw-string.shs` + `no_single_quoted_raw_string_baseline.txt` (`a929d872ddd`) | landed, **advisory**; baseline = **880** legacy sites |
| per-directory token-neutral rewrite batches | — | not started |
| lexer switch (seed + pure-Simple together) | — | blocked on the stage3 gate |
| guard → blocking; staged warnings → errors | — | after the switch, then the Win/macOS/Linux self-hosted trigger |

## Unblock condition and order

1. The bootstrap lane records a passing stage3 self-build.
2. Run the `raw_quote_migrate` batches per directory. Verify each one is
   token-neutral (same kind and value stream before and after). Ratchet the
   baseline down to 0.
3. Land the lexer switch in one PR: the seed lexer and the pure-Simple lexer
   together. Make the guard blocking in the same PR.
4. Once Windows, macOS and Linux each have a working self-hosted binary,
   promote the staged warnings to errors.

The sibling `char_condition_type_check_staged_2026-11-03` is tracked
separately and is not blocked by this item.
