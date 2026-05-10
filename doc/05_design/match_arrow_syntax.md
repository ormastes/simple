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
match_arm      := case_arm | arrow_arm
case_arm       := "case" pattern ("if" guard)? ":" expr NEWLINE
arrow_arm      := "|" pattern ("if" guard)? "->" expr NEWLINE
```

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
