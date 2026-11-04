# char_literal_lexer_switch_staged_2026-11-03

- **Status:** implemented-behind-gate (default OFF; activation blocked on the stage3 self-build)
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
| lexer switch (seed + pure-Simple together) | behind `SIMPLE_CHAR_LITERAL_LEXER=1` (PR #6592) | implemented, **default OFF**; activation blocked on the stage3 gate |
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

## Implemented behind gate (2026-11-04)

One opt-in gate, `SIMPLE_CHAR_LITERAL_LEXER` (`1`/`true`/`on`; default OFF),
read once per lexer construction in both lexers:

- Seed: `Lexer.char_literal_mode` (`src/compiler_rust/parser/src/lexer/mod.rs`,
  `CHAR_LITERAL_LEXER_ENV`, test override `with_char_literals(bool)`);
  `scan_single_quoted` / `scan_char_literal` in `lexer/strings.rs`; new
  `TokenKind::CharLit(char)`. Escapes reuse `process_escape`.
- Pure-Simple: `CoreLexer.char_literal_mode`
  (`src/compiler/10.frontend/core/lexer_struct.spl`, override
  `make_core_lexer_char_mode`), `scan_char_literal`, wire code 9
  (`TokenKind.CharLit`, `TOK_CHAR_LIT`).

ON: `'x'` is one scalar or one escape (`\n \t \r \0 \\ \' \"`, `\u{...}`,
surrogates rejected). Empty, multi-scalar and unterminated forms are lex errors
whose message names `r"..."`. `'ident` with no closing tick on the line keeps its
current meaning (seed: `Label`). OFF: token stream unchanged (legacy raw string).

Evidence:
- `cargo test -p simple-parser --lib`: 420 passed (5 new `test_char_gate_*`, ON and OFF).
- `cargo check --release --bin simple`: green.
- `test/01_unit/compiler/frontend/lexer_char_literal_gate_spec.spl`: 5/5 (ON and OFF);
  existing `lexer_indentation_eof_emits_token_spec` 6/6 and
  `lexer_reference_tokens_v1_spec` 3/3 unchanged.
- `raw_quote_migrate --dry-run --quiet src` (gate OFF, nothing written):
  `files=18559 changed=30 converted=842 kept_char=1136 escapes=47 skipped=57
  verify_failures=0`. So 842 of the 880 baselined sites are rewritable by the
  tool as-is; the rest need review (escapes/skipped).
- Guard `check-no-single-quoted-raw-string.shs` left **advisory**, baseline untouched.

Activation step 1 is done (2026-11-04, below): both parsers accept CharLit.

## Activation steps (in order)

1. **DONE 2026-11-04.** Parser/type-checker: accept `CharLit` (seed `TokenKind::CharLit`, pure-Simple
   kind 9) as a `char` literal expression in both front ends.
2. The bootstrap lane records a passing stage3 self-build.
3. Run `raw_quote_migrate --verify` per directory in batches (token-neutral),
   hand-convert the escape/skipped sites, ratchet the baseline to 0.
4. Flip the default: `SIMPLE_CHAR_LITERAL_LEXER` ON in both lexers in one PR.
5. Make `check-no-single-quoted-raw-string.shs` blocking in that same PR.
6. Promote staged warnings to errors once Windows, macOS and Linux each have a
   self-hosted binary.

## Activation step 1 done (2026-11-04)

Both parsers accept `CharLit` wherever a literal is allowed. A `char` is a
one-scalar text in both front ends today (seed HIR compares `CHAR`/`STRING`
with `rt_string_eq`; `s[i]` yields a 1-char text). So `CharLit` lowers to the
exact node the legacy `'x'` already produced, and HIR, typing and evaluation
are unchanged:

- Seed: `TokenKind::CharLit(c)` → `Expr::String(c.to_string())`
  (`expressions/primary/literals.rs`). It is accepted at expression start
  (`primary/mod.rs`), in patterns, including ranges and comma-or patterns
  (`parser_patterns.rs`), as a no-paren call argument (`no_paren.rs`), and in
  the two literal-start lookaheads in `parser_impl/core.rs`. Test hook:
  `Parser::new_with_char_literals`.
- Pure-Simple: kind 9 → `expr_raw_string_lit(value, 0)`
  (`_ParserPrimary/primary_expr.spl`). This is the no-interpolation node legacy
  `'x'` builds, so `'{'` stays literal text.
- Gate OFF: no token-kind-9 path is reachable, so parsing is byte-for-byte
  unchanged.

Evidence:
- `cargo test -p simple-parser --lib`: 424 passed (4 new, in
  `char_literal_parse_test.rs`). `cargo build --release --bin simple`: green.
- The built seed runs this program with `SIMPLE_CHAR_LITERAL_LEXER=1`, under both
  JIT and `SIMPLE_EXECUTION_MODE=interpret`:
  `val c: char = 'x'`, `s[0] == c`, `match` arms `case 'a'` / `case '\n'`.
  Output: `eq=true lit=x esc=2 a=1 other=0`. Gate OFF gives the same output.
  The control `print 'ab'` fails to parse when ON ("more than one Unicode
  scalar") and prints `ab` when OFF.
- `test/01_unit/compiler/frontend/parser_char_literal_gate_spec.spl`: 5/5.
  `lexer_char_literal_gate_spec.spl`: 5/5 unchanged.

The real `Value::Char` / `TAG_SPECIAL` representation (ADR-005
"Representation and ABI") is separate work and is not needed for this step.
