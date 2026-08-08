# Trailing-token line-continuation family — seed parser enumeration

- **ID:** seed_line_continuation_family_enumeration_2026-07-31
- **Status:** enumeration record (not a single open bug)
- **Why this exists:** three separate line-continuation gaps in the Rust seed
  parser (`023a60a05aa` comparison/equality, `a7e5fbccf85` elif-drain, and
  `seed_assignment_trailing_equals_continuation_2026-07-31` assignment) were
  each found only because something downstream broke, never by a deliberate
  sweep. This is that sweep: every construct where a line can plausibly end
  in a trailing operator/token and continue on the next line, checked with a
  parse-only probe, not by reading the parser source (reading is exactly how
  the previous three were missed).

## Method

`src/compiler_rust/parser/tests/family_continuation_probe.rs`, run via:

```
cargo test -p simple-parser --test family_continuation_probe -- --nocapture
```

One `simple_parser::Parser::new(src).parse()` call per cell; PASS/FAIL is the
literal parse result, printed with the parser's own error for FAIL cases.
Cross-checked the two already-known cases (comparison/equality shallow-elif
fixed, deep-elif still broken) against their exact pinned-test source shapes
from `023a60a05aa`/`a7e5fbccf85` to validate the probe methodology before
trusting the new results.

## Results (Rust seed parser, after the assignment fix landed)

| Construct | Continuation supported? | How determined |
|---|---|---|
| Arithmetic operators (`+`, `-`, `*`, `/`, `%`) | Yes | Probe: `val x = a +\n b` parses. Macro-generated (`parse_binary_single!`/`parse_binary_multi!`) binary parsers inherit `skip_newlines_and_indents_for_method_chain()`. |
| Logical `and` / `or` | Yes | Probe: `if a and\n b:` / `if a or\n b:` parse. Same macro-generated path. |
| Logical `not` (unary, value entirely on next line) | Yes | Probe: `val x =\n not a` parses — this is really the assignment-continuation fix (the `not` itself is unary-prefix and starts fresh on the continued line). |
| Comparison (`<`, `>`, `<=`, `>=`) | Yes | Probe passes. Fixed by `023a60a05aa` (hand-written `parse_comparison`, no longer missing the macro's continuation skip). |
| Equality (`==`, `!=`) | Yes | Probe passes. Fixed by `023a60a05aa` (hand-written `parse_equality`). |
| Plain assignment `=` | Yes | Probe passes. Fixed today, see `seed_assignment_trailing_equals_continuation_2026-07-31.md`. |
| Compound assignment (`+=`, `-=`, `*=`, `/=`, `%=`, `~=`, `~+=`, `~-=`, `~*=`, `~/=`) | Yes | Same fix site as plain `=` — all assign-op tokens share one branch in `parse_expression_or_assignment`. Probed `+=` directly; the other compound tokens go through the identical code path (also covered by `assignment_continuation_tests::compound_assign_trailing_operator_continuation_parses` for `+=`/`-=`/`*=`/`/=`/`%=`). |
| `return <expr>` with a trailing operator (`return a +\n b`) | Yes | Probe passes — goes through the ordinary expression-continuation machinery, same as any other `parse_expression()` call site. |
| `return` with the **entire** value on the next line (`return\n    a + 1`) | **No** — filed, not fixed | Probe fails: `UnexpectedToken { expected: "expression", found: "Indent" }`. See "Genuinely different mechanism" below. |
| Call-argument lists (`f(a,\n  b)`) | Yes | Probe passes. Parenthesized contexts suppress layout-token emission in the lexer (bracket-depth tracking), so this was never at risk from the trailing-operator gap class. |
| Collection literals (`[1,\n 2,\n 3]`) | Yes | Probe passes. Same bracket-depth-suppression mechanism as call arguments. |
| Member-access chains, trailing `.` (`s.\n    len()`) | Yes | Probe passes. |
| Member-access chains, leading `.` on next line (`s\n    .len()`) | Yes | Probe passes. `expressions/postfix.rs` calls `skip_newlines_and_indents_for_method_chain()` explicitly for this shape. |
| `if` condition, trailing operator | Yes | Probe passes (comparison operator continuation). |
| `while` condition, trailing operator | Yes | Probe passes (matches `023a60a05aa`'s pinned `while_condition_comparison_continuation_parses`). |
| `elif`/`else if` condition, continuation **shallower** than the branch body | Yes | Probe passes. Fixed by `a7e5fbccf85`'s `parse_elif_or_else_if_body` drain. |
| `elif`/`else if` condition, continuation **deeper** than the branch body | **No** — already filed, still open | Probe fails: `UnexpectedToken { found: "Indent" }`. Filed as `seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md` (same day as `a7e5fbccf85`); confirmed not elif-specific, reproduces identically on a primary `if`. Genuine DEDENT-then-INDENT layout/expression-continuation reconciliation, out of scope for a contained per-construct fix. |

## Genuinely different mechanism — filed, not fixed

**`return` with the value entirely on the next line** cannot be fixed the
same way as the operator-continuation and assignment-continuation gaps,
because there is no trailing token that unambiguously signals "more is
coming." `a +` cannot end a valid expression, so seeing a trailing `+`
licenses the parser to look past the Newline. `x =` similarly cannot stand
alone. But bare `return` (no value) **is** valid Simple syntax on its own —
so `return\n    <expr>` is genuinely ambiguous between "return nothing; the
indented block below is an orphaned statement" and "return this value,
wrapped onto the next line." Resolving it needs an explicit design decision
(e.g. treating a Newline+Indent immediately after a bare `return`/`break`/
`yield` as always continuing, which would silently change the meaning of any
existing bare `return` followed by an indented block — a real semantic
choice, not a parser bug). Filed separately per the task's "genuinely a
different mechanism" carve-out:
`doc/08_tracking/bug/seed_return_bare_value_next_line_ambiguity_2026-07-31.md`.

## Not covered by this sweep

Ternary (`x if cond else y`), string-literal continuation, and pattern-match
arm continuation (`case x:`) were out of the task's explicit "at minimum"
list and were not probed. If a future defect surfaces in one of those, treat
this document's absence of a row for it as "not yet checked," not "known
supported."
