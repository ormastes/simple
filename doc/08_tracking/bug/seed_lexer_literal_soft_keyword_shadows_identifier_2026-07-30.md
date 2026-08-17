# Rust-seed lexer silently reserves `literal` as an identifier, with no diagnostic naming the collision

- **Filed:** 2026-07-30
- **Severity:** medium — misleading parse error, no mention of the real cause
- **Status:** open — RE-VERIFIED STILL REPRODUCING 2026-08-17 (see below)
- **Scope:** Rust bootstrap seed only (`src/compiler_rust/`). Not reproduced against the
  pure-Simple frontend (`src/compiler/10.frontend/`) — `grep -rn '"literal"'` there finds
  no keyword table entry, so this looks seed-specific.

## Re-verification 2026-08-17 — still RED, and a static read says otherwise

Reproduced verbatim on the deployed seed:

```
$ bin/simple run /tmp/.../p_literal.spl     # var literal = 1; literal = literal + 2
error: compile failed: parse: in "p_literal.spl": Unexpected token: expected Fn, found Assign
```

**Warning for the next reader: a source-only inspection concludes, wrongly,
that this is fixed.** `TokenKind::Literal` *is* folded back into identifier
position in several places —
`parser/src/expressions/primary/identifiers.rs:86`
(`TokenKind::Literal => self.parse_keyword_identifier("literal")`),
`primary/mod.rs:104`, `helpers.rs:422,569`. Those cover EXPRESSION position,
which is exactly why the doc's own isolation found `val y = literal + "{"` and
`literal == "..."` parse fine. None of them covers **statement-level
assignment**, where the statement dispatcher must decide "is this an
assignment LHS?" before expression parsing gets a turn. So the softening is
real, partial, and does not touch the reported case.

`identifiers.rs:254` still reads `"literal" => TokenKind::Literal`
unconditionally, unlike `"lean"` and `"allow"` immediately below it, which
carry explicit comments saying they are deliberately NOT keywords.

Not fixed in this pass: the fix belongs in the statement dispatcher
(`parser/src/stmt_parsing/`), not the lexer table, and was out of budget.
Evidence quality note: run the repro; do not infer from the soft-keyword
grep.

## Symptom

The Rust seed's lexer treats the bare word `literal` as a contextual token kind
(`TokenKind::Literal`), not a plain identifier. This is presumably meant for the
seed's own meta-parsing DSL (matching `TokenKind::Literal` in pattern position —
see `parser_helpers.rs`, `expressions/primary/identifiers.rs`,
`types_def/enum_parsing.rs`), but the lexer applies it unconditionally, so any
ordinary Simple source that uses `literal` as a variable name and later
**reassigns** it breaks with a diagnostic that never mentions `literal` at all:

```
error: ... Unexpected token: expected Fn, found Assign
```

The location reported is wherever the parser's top-level recovery next
resyncs — not necessarily anywhere near the actual `literal = ...` line — because
by the time the error surfaces, the parser has already fallen back to
"expecting a new top-level `fn`" and is looking at a leftover `=` token.

## Minimal discriminating repro

Confirmed 2026-07-30 against the shared-repo Rust seed
(`src/compiler_rust/target/bootstrap/simple`, `simple run <file>`):

```simple
# repro8.spl -- PARSES FINE
fn f() -> text:
    var s = "a"
    s = s + "x"
    s

fn main():
    print(f())
```
```
$ simple run repro8.spl
ax
```

```simple
# repro7.spl -- FAILS
fn f() -> text:
    var literal = "a"
    literal = literal + "x"
    literal

fn main():
    print(f())
```
```
$ simple run repro7.spl
error: compile failed: parse: in "repro7.spl": Unexpected token: expected Fn, found Assign
```

The only difference between the two files is the variable name (`s` vs.
`literal`). Renaming `literal` -> `lit_text` (or any other non-colliding
identifier) makes the second file parse and run identically to the first.

Isolated further: `val x = "{"`, `val y = literal + "{"` (a fresh `val`
binding, not a reassignment) and `literal == "..."` (comparison) all parse
fine — it is specifically a **statement-level reassignment** whose LHS is the
bare identifier `literal` that trips the parser. Confirmed unrelated to `{`
brace content: `literal = literal + "x"` fails with no braces anywhere in
the string.

## Root cause

`src/compiler_rust/parser/src/lexer/identifiers.rs:254`:

```rust
"literal" => TokenKind::Literal,
```

This maps the identifier text `"literal"` to `TokenKind::Literal` at the
lexer level, unconditionally — there is no scoping to the contexts
(`parse_keyword_identifier("literal")` in
`expressions/primary/identifiers.rs:86`, and similar contextual call sites in
`parser_helpers.rs` and `types_def/enum_parsing.rs`) where the seed's own
grammar actually wants to recognize `literal` as a pattern keyword. Outside
those contexts, any occurrence of the bare word `literal` — including as an
ordinary user variable name — lexes as `TokenKind::Literal` rather than
`TokenKind::Ident`, and the general expression/statement parser has no
handling for `TokenKind::Literal` appearing where an identifier is expected
in an assignment LHS.

**The real defect is the missing diagnostic, not the reservation itself.**
Soft/contextual keywords are a reasonable design (many languages have them);
the problem is that when the reservation fires outside its intended context,
the resulting parse error gives no indication that `literal` was consumed as
a keyword token instead of an identifier. The error message and location are
both misleading — a developer hitting this would have no route from
`expected Fn, found Assign` back to "you used `literal` as a variable name."

## Suggested fix direction (not implemented — filing only)

Either:
1. Scope the `"literal" => TokenKind::Literal` mapping to the specific parser
   contexts that need it (parse it as `TokenKind::Ident` everywhere else,
   the same way many contextual keywords are handled — check the token text
   only where the grammar production expects it), or
2. If lexer-level reservation must stay context-free, add a parser-level
   fallback: wherever an identifier is expected and `TokenKind::Literal` is
   found instead, treat it as the identifier `"literal"` rather than failing,
   or at minimum surface a diagnostic naming the collision explicitly
   (`"literal" is a reserved word in this position`).

## Discovery context

Found while implementing a fix for
`doc/08_tracking/bug/selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30.md`
— an unrelated `var literal = ...` / `literal = literal + ...` pattern in new
interpreter code (`eval_string_lit_interpolated` in
`src/compiler/10.frontend/core/interpreter/eval.spl`) hit this exact collision
and was initially misdiagnosed as a bug in the new code before being isolated
to the variable name via the minimal repros above.
