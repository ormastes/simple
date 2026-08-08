# Bug: inline `match` value cannot be terminated by the enclosing argument/field list

- **ID:** parser_inline_match_terminated_by_list_2026-08-01
- **Date:** 2026-08-01
- **Status:** FIXED
- **Component:** `src/compiler/10.frontend/core/parser_stmts.spl` (`parse_match_arms_common`)
- **Severity:** blocker — stopped the hosted-WM showcase gate from building

## Symptom

Parsing the hosted entry with a current self-hosted compiler failed:

```
[parser_error] line 982:17: expected Indent, got Ident 'Some'
[parser_error] line 983:24: unexpected token in expression: , ','
```

(The Rust seed path reports the same defect as
`Unexpected token: expected pattern, found Comma`.)

The construct (`src/os/hosted/hosted_web_content_session.spl:978-987`) is an
inline `match` used as a struct-literal field value, where the field's
terminating comma follows the last arm:

```simple
HostedWebContentDispatch(
    event_id: event_id,
    wm_target_id: self.window_id,
    semantic_target_id: match active_route:
        Some(route): _hosted_semantic_target_id(self.browser, route)
        nil: "",
    callback_count: callback_count,
    ...
)
```

## Root cause — two defects in `parse_match_arms_common`

**1. No forced indentation.** Inside a call's parens the lexer treats the whole
parenthesized expression as one logical line and emits no NEWLINE / INDENT /
DEDENT at all. `parse_match_arms_common` unconditionally did
`parser_expect(181)` (INDENT) for the arm block, so a `match` used as an
argument or struct-literal field value always failed there first — `expected
Indent, got Ident 'Some'`. The Rust seed's `parse_match_expr` calls
`enable_forced_indentation()` before consuming the `:` for exactly this reason;
the self-hosted parser had the lexer support
(`CoreLexer.enable_forced_indentation`, already used by the block-bodied lambda
path in `_ParserPrimary/primary_expr.spl`) but never called it for `match`.

**2. Arm loop had no list terminator.** With indentation forced on, the arm
block gets a real INDENT but still no DEDENT before the enclosing list's
terminator — the `,` / `)` / `]` / `}` shares the last arm's line, so the lexer
has not flushed a DEDENT yet. The arm loop only stopped on DEDENT (182) or EOF
(190); anything else fell through to the caseless-arm branch and was handed to
`parse_expr` as if it began another pattern.

Both halves are already solved for block-bodied lambdas in
`_ParserPrimary/primary_expr.spl` (enable forced indentation around the body;
treat `)`, `,` and EOF as terminators, leave them unconsumed, and
`lex_pop_indent()` to resync the lexer's indent stack). The `match` arm loop
never got the same treatment.

## Shape matrix

Measured with two stage2 compilers built from `ccc28893274` — one pristine, one
patched — driven through the **pure-Simple** `CompilerDriver`
(`simple native-build <file.spl> -o out --backend llvm`; note that the
`--entry` form delegates to the Rust runtime path instead).

| # | shape | before | after |
|---|-------|--------|-------|
| a01 | inline `match` as struct-literal field, comma-terminated | `unexpected token in expression: , ','` | parses |
| a02 | inline `match` as LAST struct-literal field, `)`-terminated | `... : ) ')'` | parses |
| a03 | inline `match` as call argument, comma-terminated | `... : , ','` | parses |
| a04 | inline `match` as array element, comma-terminated | `... : , ','` | parses |
| a05 | inline `match` as dict value, `}`-terminated | `... : } '}'` | parses |
| a08 | nested inline `match` inside an arm, comma-terminated | `... : , ','` | parses |
| a09 | `case`-spelled arms, comma-terminated | `... : , ','` | parses |
| a13 | inline `match` as last call argument, `)` on the arm's line | `... : ) ')'` | parses |
| a06 | inline `if/else` as struct field, comma-terminated | parses | parses |
| a07 | inline `if/else` as last struct field | parses | parses |
| a10 | `match` bound to a local, then used | parses | parses |
| a11 | statement-position `match` | parses | parses |
| a12 | `match` as a function's return value | parses | parses |

Inline `if/else` is NOT in the family: `parse_if_expr` runs no arm loop and
needs no INDENT, so `reason: if changed: "" else: "..."` on the next line of the
hosted file was never a blocker.

## Fix

`src/compiler/10.frontend/core/parser_stmts.spl`, `parse_match_arms_common`:

1. `lex_enable_forced_indentation()` before consuming the `:`, and
   `lex_disable_forced_indentation()` when the arm list ends.
2. Break the arm loop on `TOK_COMMA` / `TOK_RPAREN` / `TOK_RBRACKET` /
   `TOK_RBRACE`, leaving the terminator unconsumed for the enclosing list
   parser and calling `lex_pop_indent()` (only when an INDENT was actually
   consumed) to resync the lexer's indent stack.

## Next blocker (separate, pre-existing)

With this fix in, `hosted_web_content_session.spl` itself parses; its import
closure then stops at a DIFFERENT and unrelated defect, reproduced identically
by the pristine and the patched compiler:

```
[parser_error] path src/lib/common/web/public_suffix_data.spl line 10012:25: expected ], got , ','
```

That file is a flat array literal of ~10,000 string elements, so this looks like
an element-count cap in the self-hosted array-literal parser. Not filed here —
it needs its own bug.

## Regression coverage

`test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl` — the
declarations are themselves the grammar coverage (a parse error means the file
does not load) and the `it` blocks assert each inline match still selects the
right arm.
