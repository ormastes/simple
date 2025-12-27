# Feature #1000: Predicate Grammar

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #1000 |
| **Feature Name** | Predicate Grammar |
| **Category** | AOP |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

The `pc{...}` syntactic island introduces a unified predicate grammar for AOP weaving, DI binding, and architecture rules. It provides:
- Boolean operators: `!`, `&`, `|`
- Pattern wildcards: `*`, `**`, prefix*, *suffix
- Signature patterns for function matching
- Context-aware validation

## Specification

[research/aop.md](../../research/aop.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/predicate_parser.rs` | Predicate parser (lines 26-30) |
| `src/compiler/src/predicate.rs` | Predicate evaluation |

### Key Components

- **Lexer Mode**: `pc{...}` triggers predicate parsing mode
- **Boolean Operators**: Standard logical operations
- **Pattern Matching**: Wildcard support for flexible matching
- **Signature Patterns**: Function signature matching

## Grammar (EBNF)

```ebnf
expr        ::= or_expr
or_expr     ::= and_expr ( '|' and_expr )*
and_expr    ::= not_expr ( '&' not_expr )*
not_expr    ::= '!' not_expr | primary
primary     ::= selector | '(' expr ')'
selector    ::= name '(' args? ')'
pattern     ::= seg ('.' seg)*
seg         ::= IDENT | '*' | '**' | IDENT '*' | '*' IDENT
signature   ::= ret_pat ' ' qname_pat '(' arg_pats ')'
```

## Examples

```simple
# Match all handle* methods in service package
pc{ execution(*.handle*(..)) & within(service.**) }

# Match methods without @internal attribute
pc{ execution(*.*(..)) & !attr(internal) }

# Match type bindings for UserRepository
pc{ type(UserRepository) & within(domain.**) }
```

## Dependencies

- Depends on: #1 Lexer, #2 Parser
- Required by: #1006-#1050 (all AOP features)

## Notes

- Foundation for all AOP functionality
- Designed for IDE autocomplete support
- Unified across weaving, DI, and architecture contexts
