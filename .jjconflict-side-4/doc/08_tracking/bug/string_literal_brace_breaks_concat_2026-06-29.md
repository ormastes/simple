# Bug: unescaped `{` in a string literal corrupts `+` concatenation in the same expression

- **ID:** string_literal_brace_breaks_concat_2026-06-29
- **Severity:** P2 (silently emits the source `" + var + "` verbatim → invalid CSS/JSON, blank web render)
- **Area:** language / interpreter (string-literal interpolation lexing)
- **Status:** FIXED (seed parser) 2026-07-28 — see [Fix history](#fix-history) below.
  App-level workaround remains in `src/os/compositor/simple_web_window_renderer.spl` (harmless).

## Summary
When a string literal containing an **unescaped single `{`** is part of a `+`
concatenation expression, the interpolation scanner does not stop at the literal's
closing `"`. It swallows the `" + var + "` operators (and everything up to the next
`}`) as interpolation/literal text, so the concatenated variables are never
substituted — the raw source `" + var + "` appears verbatim in the output.

## Minimal repro (confirmed on `release/x86_64-unknown-linux-gnu/simple`, interpreter path)
```simple
var x = "VAL"
print "a " + x + " b"        # => "a VAL b"           (OK, no brace)
print "p { " + x + " }"      # => "p  + x + "          (WRONG)
print "p { q: " + x + "; }"  # => "p { q: " + x + "; }" (WRONG — verbatim)
```

## Real-world impact
`_simple_web_window_css` built its theme CSS with `":root { --glass-accent: " + accent + "; ... }"`.
Every `+ color +` was emitted verbatim, so the rendered CSS carried no real colors →
all-white frame. This broke `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl`
("exposes SimpleOS app pixels through the common web render artifact": `_count_changed == 0`).

## Workaround (used in the fix)
Build such strings with interpolation `{var}` plus **escaped** literal braces
`\{` / `\}` (both confirmed to round-trip to a single literal brace, no stray backslash):
```simple
":root \{ --glass-accent: {accent}; \} ..."
```

## Expected behavior
The interpolation scanner must terminate at the string literal's closing `"`; a `{`
with no matching `}` inside the same literal should be a literal brace (or a lex error),
never consume following concatenation operators.

## Fix history

Three landings, in `src/compiler_rust/parser/src/lexer/strings.rs` (the f-string
interpolation expression scanner). **Note for future audits: this fix was never
lost to the jjconflict-tree revert incident** — the middle commit deliberately
narrowed the first one, and the audit in
`doc/09_report/open_bug_doc_staleness_audit_2026-07-27.md` misread that as a lost fix.

1. **`ca58e1f69b5`** `fix(seed-parser): contain unmatched f-string braces` (2026-07-17).
   In a non-triple f-string, ANY unescaped `"` at top level of an interpolation
   expression was treated as the OUTER string's closing quote → `expr_failed`,
   backtrack, `{` becomes a literal brace. Fixed this bug.
2. **`310bcdf1131`** `fix(release-sanity): seed f-string lexer nested-quote regression`
   (2026-07-17, same day). **Reverted the quote guard from (1)** because it was too
   broad: it silently miscompiled legitimate nested quotes such as `"{xs.join("-")}"`
   and caused stage1 parse failures. Runaway braces were instead contained by a
   **newline guard** (`c == '\n' && !is_triple` → `expr_failed`). That guard fixes
   the multi-line runaway case, but **cannot see this bug**, which is entirely on one
   line — so this defect regressed and stayed open.
3. **`055c64cfb30`** (2026-07-28) — forward fix reconciling both. In a
   non-triple f-string, an unescaped `"` may only **open** a nested string where
   an operand is genuinely expected; otherwise it closes the OUTER string →
   `expr_failed` backtrack, exactly as (1) intended. "Operand expected" is
   `paren_depth > 0` (inside a call or index — the context the (2) regressions
   needed: `join("-")`, `map("{_}")`), **or**, at `paren_depth == 0`, the
   scanned expression so far ends in a binary/logical operator or separator
   (`== != <= >= < > + - * / % , ( [`, or a word-boundary `and`/`or`/`not`/`in`),
   **or** it contains an `if`/`else`/`match` word (inline conditionals and match
   arms legitimately hold bare string literals). This is the
   `Self::nested_string_may_open(&expr)` helper in the same file. Triple
   f-strings keep the fully permissive form; escaped `\"` is still handled by the
   backslash arm; the (2) newline guard is retained unchanged.

   Regression tests in `src/compiler_rust/parser/src/fstring_bug_tests.rs`:
   `test_literal_brace_does_not_swallow_same_line_concat` and
   `test_literal_brace_with_colon_does_not_swallow_same_line_concat` pin the
   repro above, and `test_top_level_quote_in_operand_position_is_still_interpolation`
   pins the `{key != ""}` / `{if dry: "on" else: "off"}` cases that the narrower
   `paren_depth > 0`-only rule would have broken. The (2) nested-quote tests
   still pass — `cargo test -p simple-parser` is fully green — so this is a
   forward delta, not a revert.

   **Scope: seed (Rust) parser only.** The pure-Simple self-hosted lexer
   (`src/compiler/10.frontend/core/`) was not touched by this landing; the
   deployed `bin/simple` seed binary reproduced the bug until rebuilt from this
   commit. If the self-hosted lexer carries the same single-line runaway, it
   needs the same treatment — verify before assuming parity.

The hir-level companion test from (1),
`unmatched_literal_brace_does_not_consume_later_function_scope` in
`src/compiler_rust/compiler/src/hir/lower/tests/seed_regression_tests.rs`, survived
all three landings and still passes.

## Related
- [[string_literal_double_brace_collapse_2026-06-16]] — sibling brace-in-literal defect (`{{`/`}}` collapse).
- [[angle_bracket_index_lint_parse_mismatch_2026-06-06]] — separate JIT generics-vs-index
  false positive (`rules[pos] < x`) that forces compositor specs onto the interpreter path
  where this bug surfaces.
