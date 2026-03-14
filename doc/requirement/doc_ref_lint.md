# REQ: Doc Reference & SDoctest Lint

**Feature:** `doc_ref_lint`
**Status:** Draft
**Related:** [plan](../plan/doc_ref_lint.md) | [design](../design/doc_ref_lint.md) | [test](../../test/system/doc_ref_lint_spec.spl)

---

## Motivation

Public functions and classes need documentation with executable examples (sdoctest). Currently there is no way to:
1. Reference other functions/classes from doc comments
2. Delegate sdoctest to a related function (avoid duplicating examples)
3. Lint-check that references are valid and sdoctest coverage is complete

## Scope

### In Scope
- Doc comment reference syntax (`@see` and `@sdoctest`)
- Lint pass `public_doc.spl` in `src/compiler/35.semantics/lint/`
- Integration with existing doc-coverage tooling

### Out of Scope
- Rendering references as hyperlinks (future IDE feature)
- Cross-module reference resolution (same module only for v1)
- Markdown doc file references (only `.spl` doc comments)

---

## Reference Syntax

Two new markers inside `"""..."""` doc comments:

### `@see(name)`
Reference another function or class in the same module.

```simple
"""
Parses a token from the input stream.
@see(Lexer)
@see(parse_expression)
"""
fn parse_token(input: text) -> Token:
    ...
```

### `@sdoctest(name)`
Delegate sdoctest to another function or class. Means: "my executable examples are in `name`'s docstring."

```simple
"""
Shorthand for parse_token — delegates examples.
@sdoctest(parse_token)
"""
fn parse(input: text) -> Token:
    parse_token(input)
```

---

## Lint Rules

| Code | Severity | Condition | Message |
|------|----------|-----------|---------|
| PDOC001 | WARNING | Public `fn` has no sdoctest block AND no `@sdoctest(X)` link | `public function 'X' missing sdoctest or @sdoctest link` |
| PDOC002 | WARNING | `@see(X)` or `@sdoctest(X)` where `X` does not exist in module | `doc reference '@see(X)' targets unknown name 'X'` |
| PDOC003 | WARNING | `@see(X)` where `X` is never used in the function body | `doc reference '@see(X)' but 'X' is not used in function body` |
| PDOC004 | WARNING | `@sdoctest(X)` links to fn but `X` is a class, or vice versa | `@sdoctest(X) type mismatch: 'X' is a class, expected function` |
| PDOC005 | WARNING | `@sdoctest(X)` target `X` itself has no sdoctest block | `@sdoctest(X) target 'X' has no sdoctest block either` |

### Rule Details

**PDOC001 — Missing sdoctest on public function:**
- Applies to: `fn` declarations (not `me` methods, not `static fn` for v1)
- Exempt: `extern fn`, functions with `pass_todo`/`pass_do_nothing`/`pass_dn`
- A function satisfies this rule if it has EITHER:
  - An `sdoctest:` block in its `"""` doc comment
  - An `@sdoctest(other_fn)` reference to a function that has an sdoctest block

**PDOC002 — Invalid reference target:**
- Parses `@see(X)` and `@sdoctest(X)` from doc comment text
- Resolves `X` against module-level declarations (functions, classes, structs, enums, traits)
- If `X` is not found, emit warning

**PDOC003 — Unused @see reference:**
- Only applies to `@see`, NOT to `@sdoctest`
- Scans function body for identifier references to `X`
- If `X` appears nowhere in the body (not called, not instantiated, not type-referenced), warn

**PDOC004 — Type mismatch on @sdoctest:**
- `@sdoctest(X)` on a `fn` → `X` must be a `fn` (not class/struct/enum)
- `@sdoctest(X)` on a `class` → `X` must be a `class`
- Mismatches produce a warning

**PDOC005 — Chained delegation with no sdoctest:**
- If `fn a` has `@sdoctest(b)` and `fn b` also has no sdoctest, warn on `fn a`
- Prevents infinite delegation chains

---

## I/O Examples

### Example 1: Valid sdoctest delegation

```simple
"""
Computes factorial iteratively.

sdoctest:
    expect(factorial(0)).to_equal(1)
    expect(factorial(5)).to_equal(120)
"""
fn factorial(n: i64) -> i64:
    var result = 1
    var i = 1
    while i <= n:
        result = result * i
        i = i + 1
    result

"""
Computes factorial recursively. Same behavior as factorial().
@sdoctest(factorial)
"""
fn factorial_recursive(n: i64) -> i64:
    if n <= 1: 1
    else: n * factorial_recursive(n - 1)
```

**Lint output:** No warnings (factorial_recursive delegates to factorial which has sdoctest).

### Example 2: Missing sdoctest

```simple
fn helper(x: i64) -> i64:
    x + 1
```

**Lint output:**
```
[PDOC001] WARNING: public function 'helper' missing sdoctest or @sdoctest link
```

### Example 3: Invalid reference

```simple
"""
@see(nonexistent_function)
"""
fn process(data: text) -> text:
    data.trim()
```

**Lint output:**
```
[PDOC002] WARNING: doc reference '@see(nonexistent_function)' targets unknown name 'nonexistent_function'
```

### Example 4: Unused @see

```simple
"""
@see(Lexer)
"""
fn add(a: i64, b: i64) -> i64:
    a + b
```

**Lint output:**
```
[PDOC003] WARNING: doc reference '@see(Lexer)' but 'Lexer' is not used in function body
```

### Example 5: Type mismatch

```simple
class Parser:
    """Parser for tokens."""
    input: text

"""
@sdoctest(Parser)
"""
fn parse(input: text) -> Token:
    ...
```

**Lint output:**
```
[PDOC004] WARNING: @sdoctest(Parser) type mismatch: 'Parser' is a class, expected function
```

---

## Acceptance Criteria

- [ ] AC1: `@see(name)` and `@sdoctest(name)` parsed from doc comments
- [ ] AC2: PDOC001 warns on public `fn` without sdoctest or `@sdoctest` link
- [ ] AC3: PDOC002 warns on references to non-existent names
- [ ] AC4: PDOC003 warns on `@see(X)` where X is unused in body
- [ ] AC5: PDOC004 warns on `@sdoctest` type mismatches (fn vs class)
- [ ] AC6: PDOC005 warns on chained delegation with no terminal sdoctest
- [ ] AC7: Lint integrates into `bin/simple build lint` pipeline
- [ ] AC8: Existing tests unaffected

---

## Dependencies

- `src/compiler/35.semantics/lint/__init__.spl` — already exports `public_doc.*`
- `src/compiler/10.frontend/parser/doc_gen.spl` — doc comment extraction
- Arena-based core AST (`compiler.core.ast`, `compiler.core.ast_expr`)
