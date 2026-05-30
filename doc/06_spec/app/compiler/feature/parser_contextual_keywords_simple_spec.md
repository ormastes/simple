# Contextual Keyword Disambiguation

**Feature ID:** #PARSER-012 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/parser_contextual_keywords_simple_spec.spl`_

---

## Overview

Simple treats `skip`, `static`, and `default` as contextual keywords rather than
fully reserved words. This means each token can serve as either a keyword or an
ordinary identifier depending on syntactic context -- specifically, whether it is
followed by `(`. The spec validates all six disambiguation branches (keyword vs
identifier for each of the three tokens), confirms that multiple contextual
keywords can coexist as method names within a single class, and ensures that
identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never
misinterpreted.

## Syntax

```simple
# skip as identifier (followed by '(')
fn skip(n):
    return n * 2
val result = skip(5)

# skip as keyword (standalone statement)
skip

# static as keyword in method declaration
class Math:
    static fn add(a, b):
        return a + b
Math.add(3, 7)

# default as identifier on a class method
class Settings:
    fn default():
        return 200
settings.default()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Contextual keyword | A token that acts as a keyword or identifier based on surrounding syntax |
| Lookahead disambiguation | The parser checks for a following `(` to decide identifier vs keyword |
| Branch coverage | All six branches (keyword/identifier x three tokens) are exercised |
| Coexistence | A single class can define methods named `skip`, `static`, and `default` |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 12 |

## Test Structure

### skip as identifier

- ✅ works as function name
- ✅ works as method name
### skip as keyword

- ✅ works as standalone statement
- ✅ works in function body
### static as identifier

- ✅ works as function name
- ✅ works as method name
### static as keyword

- ✅ works in static method declaration
### default as identifier

- ✅ works as function name
- ✅ works as method name
### default as keyword

- ✅ parses in match context
### edge cases

- ✅ allows all three keywords as method names in same class
- ✅ distinguishes keywords from underscored identifiers

