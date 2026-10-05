# Comment-only block body silently swallows the next statement (2026-10-04)

**Severity:** P1 — silent miscompile, no diagnostic.
**Components:** pure-Simple parser `src/compiler/10.frontend/core/parser_stmts.spl`
`parse_block` (flat-body rule, lines ~391-398); Rust seed parser shows the same behavior.

## Rule

A block must contain at least one statement. A deliberate empty body is written
with `pass` (optional rationale: `pass("why")`) or `pass_todo` / `pass_do_nothing`
/ `pass_dn` (rationale required, `REQC001` otherwise). A body made only of
comments is not a body and must be a parse error. The seed may tolerate it; the
pure-Simple compiler must not.

## Repro

```simple
fn main() -> i64:
    if false:
        # nothing
    print "after-if"
    0
```

Expected: parse error (empty `if` body; use `pass`).
Actual (seed `simple run`, 2026-10-04, built from origin/main + #2459): no error and
**`after-if` is never printed** — the comment line produces no Indent, so the
next statement at the header's column is taken as the `if` body ("flat body").
With `if true:` it looks correct by accident.

Inconsistent across headers (same seed): comment-only `fn`, `for` and `class`
bodies are rejected (`expected Indent`), comment-only `if` is accepted.

## Pure-Simple logic

`parse_block` accepts a body on a later line at the SAME column as its header
when the next token can start a statement (`parse_block_flat_body_can_start`).
After a comment-only line the lexer emits no Indent, so a following sibling
statement satisfies that rule and is consumed as the body. The comment above the
rule says a header with no body "is a parse error", but a following sibling
statement defeats that check.

## Fix direction

Reject the flat body when the body line is at the header's own indentation (a
sibling, not a body), or track that the only lines between the header and the
next token were comments and require Indent then. Error text should say
`empty block: use pass("reason")`. Add a regression spec covering `if`, `elif`,
`else`, `while`, `for`, `match` arms, `fn`, `class`.
