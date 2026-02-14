# Simple Language Grammar

Part of [Lexer and Parser Specification](lexer_parser.md).

This document defines the complete Tree-sitter grammar for the Simple language. Due to its size, it is split into two parts:

## Contents

| Part | Description | Lines |
|------|-------------|-------|
| [Part 1: Definitions](lexer_parser_grammar_definitions.md) | Types, structs, classes, enums, traits, modules | ~700 |
| [Part 2: Statements & Expressions](lexer_parser_grammar_expressions.md) | Statements, patterns, expressions, operators | ~750 |

## Grammar Overview

The grammar uses:
- **GLR parsing** for ambiguity resolution
- **External scanner** for indentation-based syntax (INDENT/DEDENT)
- **Precedence declarations** for operator binding

### Section Summary

**Part 1 - Definitions:**
- Source file structure
- Decorators and attributes
- Type system (simple, generic, pointer, tuple, array, dict, function, union, optional)
- Struct definitions
- Class definitions
- Enum definitions
- Trait definitions
- Impl blocks
- Actor definitions
- Handle pool definitions
- Function definitions
- Macro definitions
- Global declarations
- Module system (use, common use, export use, auto import)
- Unit types

**Part 2 - Statements & Expressions:**
- Statements (let, return, break, continue, pass, send)
- Compound statements (if, match, for, while, loop, with, receive)
- Patterns (identifier, literal, wildcard, tuple, struct, enum, or, range, rest, typed)
- Expressions (primary, unary, binary, comparison, logical)
- Special expressions (try, if-expr, match-expr, lambda)
- Comprehensions (list, dict)
- Spread expressions
- Comments

## Tier-Based Grammar Docs

Generated reference docs organized by compilation tier:

| Doc | Description |
|-----|-------------|
| [Seed Grammar](../grammar/seed_grammar.md) | C++ bootstrap compiler — minimal subset |
| [Core Grammar](../grammar/core_grammar.md) | Simple-in-Simple compiler — self-hosting |
| [Full Grammar](../grammar/full_grammar.md) | Complete runtime — all features |
| [Keyword Reference](../grammar/keyword_reference.md) | All keywords in one table |
| [Tree-sitter Status](../grammar/treesitter_status.md) | highlights.scm consistency report |

Source of truth: [`doc/spec/grammar/tier_keywords.sdn`](../grammar/tier_keywords.sdn)

Generate with: `bin/simple grammar-doc`

---

Next: [Part 1: Definitions](lexer_parser_grammar_definitions.md)
