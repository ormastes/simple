# Seed parser: `return` with its value entirely on the next line is ambiguous with bare `return` — NOT FIXED, needs a design decision

- **ID:** seed_return_bare_value_next_line_ambiguity_2026-07-31
- **Status:** open, filed rather than forced — found while enumerating the
  line-continuation family for
  `seed_assignment_trailing_equals_continuation_2026-07-31.md`
- **Severity:** low — no known real-source occurrence found; `return a +\n b`
  (value starting on the `return` line, continuing via a trailing operator)
  already works fine, which covers the natural line-wrap case

## Symptom

```
fn f(a: i64) -> i64:
    return
        a + 1
```

fails to parse:

```
UnexpectedToken { expected: "expression", found: "Indent" }
```

## Why this is NOT the same defect class as the assignment/comparison/elif fixes

Every other continuation gap fixed this week (`023a60a05aa`, `a7e5fbccf85`,
`seed_assignment_trailing_equals_continuation_2026-07-31`) has a trailing
token that **cannot** end a valid expression or statement on its own — a
dangling `+`, `==`, `and`, or bare `=` unambiguously means "more follows."
The fix in each case is mechanical: skip the Newline/Indent right after that
token and drain the matching Dedent later.

`return` has no such unambiguous trailing token. Bare `return` (no value) is
itself a complete, valid statement in Simple —
`src/compiler_rust/parser/src/stmt_parsing/jump.rs::parse_return` checks
`!self.check(&TokenKind::Newline)` and, on a Newline, produces
`ReturnStmt { value: None }`. So `return\n    <expr>` is genuinely ambiguous
between:

1. "Return nothing; the indented block below is a separate, malformed
   statement" (today's behavior — which is why it currently errors instead
   of silently doing the wrong thing: nothing else can legally open a block
   there, so it surfaces as a parse error rather than silently returning
   nil).
2. "Return `<expr>`, which happens to be wrapped onto the next line."

Fixing this means picking one of those meanings for every `return`/`break`/
`yield` immediately followed by a Newline+Indent — a semantic decision that
changes what bare `return` followed by an indented block means, not a
mechanical parser continuation fix.

## Non-occurrence check

Searched for this shape in-tree; found no real source file relying on it
(unlike the assignment case, which had a live blocking instance at
`hosted_browser_renderer_worker.spl:1066`). `return a +\n b` (trailing
operator, not bare `return`) already parses today via the ordinary
expression-continuation machinery, which covers the natural "value doesn't
fit on one line" case without this ambiguity.

## Recommendation (not applied)

If this needs future support: require the value to start on the `return`
line and only continue via a trailing operator (already works), or introduce
an explicit continuation marker for the bare-then-indented shape, and audit
every existing bare-`return`-followed-by-indented-block in the codebase
before changing the default meaning — a silent flip would change return
value semantics, not just fix a parse error.

## Related

`seed_assignment_trailing_equals_continuation_2026-07-31.md`,
`doc/08_tracking/bug/seed_line_continuation_family_enumeration_2026-07-31.md`
(full family table).

## Resolution (2026-11-04)

The self-hosted parser (`parser_stmts.spl`, `kind == 49`) also treats `return` + Newline as a bare return, so both parsers reject the shape. No grammar change: the seed now emits
"`return` value must be on the same line as `return`" when bare `return` is followed by Newline + Indent
(`jump.rs::parse_return`). Test: `src/compiler_rust/parser/tests/return_value_next_line_diagnostic.rs`.
