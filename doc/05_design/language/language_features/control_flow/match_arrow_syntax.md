# Match Arrow Syntax Design

## Overview

Add Erlang-inspired `| pattern -> expr` syntax as alternative to `case pattern: expr` in match expressions.

## Syntax Comparison

```simple
# Current syntax (verbose)
match x:
    case 0: "zero"
    case 1: "one"
    case _: "other"

# New syntax (preferred - shorter)
match x:
    | 0 -> "zero"
    | 1 -> "one"
    | _ -> "other"

# Mixed (allowed but not recommended)
match x:
    case 0: "zero"
    | 1 -> "one"
    | _ -> "other"
```

## Grammar

```ebnf
match_expr     := "match" expr ":" NEWLINE INDENT match_arms DEDENT
match_arms     := match_arm+
match_arm      := case_arm | arrow_arm | caseless_arm
case_arm       := "case" pattern ("if" guard)? ":" body
arrow_arm      := "|" pattern ("if" guard)? "->" body
caseless_arm   := pattern ("if" guard)? ("as" IDENT)? separator body
separator      := ":" | "=>" | "->"
body           := expr NEWLINE | statement NEWLINE | NEWLINE INDENT statement+ DEDENT
```

**`caseless_arm` was missing from this grammar until 2026-09-06 and is the form
the codebase actually uses most.** Both compilers accept a match arm with
neither the `case` keyword nor a leading `|` — `Ok(v): ...`, `0 => "zero"`,
`0 -> "zero"` — and its body may be a statement (`Err(m) -> return Err(m)`) or an
indented block, not only an expression. The `->` spelling of it was accepted by
the Rust seed from the start but rejected by the self-hosted parser until
`doc/08_tracking/bug/stage3_selfhost_parser_rejects_arrow_match_arms_2026-09-06.md`,
which blocked Stage 3.

**Known gap, not described by this grammar:** `arrow_arm` with an INLINE body
parses only as the LAST arm, on both compilers —
`doc/08_tracking/bug/inline_arrow_match_arm_fails_when_followed_by_another_arm_2026-09-05.md`.
The "Precedence" section below still recommends that spelling; treat the
recommendation as aspirational until that bug is fixed.

## Precedence

`| ->` is **preferred** over `case:` because:
1. Shorter (3 chars vs 6 chars)
2. Erlang/Haskell/OCaml familiarity
3. Visual alignment with `|` creates cleaner code

## Examples

### Simple Values
```simple
match status:
    | 200 -> "OK"
    | 404 -> "Not Found"
    | 500 -> "Server Error"
    | _ -> "Unknown"
```

### With Guards
```simple
match n:
    | 0 -> "zero"
    | x if x < 0 -> "negative"
    | x if x > 0 -> "positive"
```

### Destructuring
```simple
match result:
    | Ok(value) -> handle(value)
    | Err(e) -> log_error(e)
```

### Multi-line Body
```simple
match cmd:
    | "start" ->
        init()
        run()
    | "stop" ->
        cleanup()
        exit()
```

## Implementation Files

### Rust (simple_old)
- `src/rust/parser/src/expressions/primary/control.rs` - parse match arms
- `src/rust/parser/src/token.rs` - add `Pipe` and `Arrow` tokens if missing

### Simple (self-hosted)
- `simple/compiler/parser.spl` - update match parsing

## Migration

1. Both syntaxes work simultaneously
2. Linter suggests `| ->` when `case:` is used
3. Future: auto-fix migration tool
