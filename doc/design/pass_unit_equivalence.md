# Design Decision: `pass` and `()` Equivalence

**Status:** Implemented
**Date:** 2026-01-30
**Category:** Control Flow, Language Design

---

## Summary

Simple supports both `pass` (Python-style no-op statement) and `()` (Rust-style unit value) as **synonymous ways** to express "do nothing" in statement/expression contexts.

---

## Motivation

### The Problem

Different programming paradigms handle "empty" or "no-op" differently:

1. **Statement-oriented languages (Python):** Use explicit `pass` keyword
2. **Expression-oriented languages (Rust, Scala):** Use unit value `()`

Simple aims to be approachable to developers from both backgrounds while maintaining expression-oriented design.

### The Solution

Support **both** syntaxes as synonyms:

```simple
# Both are valid and equivalent:
match value:
    Some(x): process(x)
    None: ()      # Unit value (expression)

match value:
    Some(x): process(x)
    None: pass    # No-op statement
```

---

## Design

### Implementation

**Lexer:** Recognizes `pass` as keyword → `TokenKind::Pass`
```rust
// src/rust/parser/src/lexer/identifiers.rs:108
"pass" => TokenKind::Pass,
```

**Parser:** Dispatches to `parse_pass()`
```rust
// src/rust/parser/src/parser_impl/core.rs:453
TokenKind::Pass => self.parse_pass(),
```

**AST:** Creates `PassStmt` node
```rust
// src/rust/parser/src/stmt_parsing/jump.rs:71-83
pub(crate) fn parse_pass(&mut self) -> Result<Node, ParseError> {
    let start_span = self.current.span;
    self.expect(&TokenKind::Pass)?;

    Ok(Node::Pass(PassStmt {
        span: Span::new(...),
    }))
}
```

**Codegen:** Both `pass` and `()` compile to identical no-op

### Type System

- **`()`:** Has type `()` (unit type), is an expression
- **`pass`:** Is a statement, semantically equivalent to `()`

Both can be used anywhere a "do nothing" is needed.

---

## Usage Guidelines

### When to Use `()`

**Preferred in expression contexts:**

```simple
# Match expressions returning values
val result = match opt:
    Some(x): x
    None: ()  # Returns unit value

# Function returning unit
fn log_if_enabled(msg: text) -> ():
    if not LOGGING_ENABLED:
        return ()  # Explicit early return with unit
    write_log(msg)
```

**Benefits:**
- Consistent with expression-oriented design
- Clear type: returns `()` (unit)
- Familiar to Rust/Scala developers

### When to Use `pass`

**Preferred when intent is "explicitly doing nothing":**

```simple
# Placeholder in development
match msg_type:
    "info": log_info(msg)
    "warn": log_warn(msg)
    "error":
        pass  # TODO: Implement error logging
    _: ()

# Explicit no-op in conditional
if condition:
    process_data()
else:
    pass  # Intentionally do nothing in else branch
```

**Benefits:**
- Familiar to Python developers
- Explicit intent: "I'm intentionally doing nothing here"
- Clear as placeholder during development

---

## Comparison with Other Languages

| Language | Empty/No-op Syntax | Philosophy |
|----------|-------------------|------------|
| **Python** | `pass` | Statement-oriented |
| **Rust** | `()` | Expression-oriented |
| **Scala** | `()` | Expression-oriented |
| **Ruby** | `nil` | Expression-oriented |
| **Go** | (empty block) | Statement-oriented |
| **Simple** | `()` **or** `pass` | **Both** (flexible) |

---

## Trade-offs

### Advantages

✅ **Familiar to multiple communities**
- Python developers recognize `pass`
- Rust/Scala developers recognize `()`

✅ **Flexibility**
- Choose based on context and clarity
- Use `()` for expression semantics
- Use `pass` for explicit no-op intent

✅ **No breaking changes**
- `pass` already implemented (Python heritage)
- `()` already supported (expression-oriented design)

### Disadvantages

❌ **Two ways to do the same thing**
- Potential style inconsistency
- Need to document when to use which

❌ **Slight conceptual overhead**
- Developers need to understand both forms
- Teaching burden: "Are they different?"

---

## Recommendations

### For Application Code

**Use `()` by default** (expression-oriented):

```simple
match result:
    Ok(val): val
    Err(_): ()  # Clear: returns unit
```

**Use `pass` for clarity when needed:**

```simple
match state:
    Active: process()
    Paused:
        pass  # Explicit: "intentionally paused, doing nothing"
    Stopped: cleanup()
```

### For Library Code

**Prefer `()` for consistency:**

```simple
fn noop() -> ():
    ()  # Clear return type and value
```

---

## Examples

### Equivalence in Match Arms

```simple
# Both work identically:

val x = Some(42)

match x:
    Some(v): print(v)
    None: ()      # Returns unit value

match x:
    Some(v): print(v)
    None: pass    # No-op statement
```

### Equivalence as Statements

```simple
# Both work as standalone statements:

fn placeholder():
    pass  # TODO: Implement

fn placeholder2():
    ()    # TODO: Implement
```

### Equivalence in Conditionals

```simple
# Both work in if branches:

if enabled:
    run_task()
else:
    ()    # Do nothing

if enabled:
    run_task()
else:
    pass  # Do nothing
```

---

## Testing

**Spec Test:** `test/system/features/control_flow/pass_unit_equivalence_spec.spl`

Verifies:
- Both work in match arms
- Both work as standalone statements
- Both work in if-else branches
- Both work in loops
- Both compile to identical code

---

## Documentation

1. **Syntax Reference:** `doc/guide/syntax_quick_reference.md`
   - Section: "Empty Statements / No-op"
   - Documents both forms and when to use each

2. **CLAUDE.md:**
   - Quick reference showing both syntaxes
   - Notes they're synonyms

3. **This Document:**
   - Design rationale
   - Implementation details
   - Usage guidelines

---

## Future Considerations

### Should We Deprecate One?

**No** - both have value:
- `()` aligns with expression-oriented design
- `pass` provides clarity of intent

Deprecating either would:
- Break existing code
- Reduce flexibility
- Alienate developers from that tradition

### Could We Lint for Consistency?

**Possible lint rule:**
```
prefer_unit_over_pass:
  description: "Prefer () over pass for consistency"
  level: suggestion  # Not error
  autofix: true
```

But this should remain **optional** - both are valid style choices.

---

## Conclusion

Simple's support for both `pass` and `()` is a **pragmatic design decision** that:

1. **Respects language heritage** - Simple draws from both Python and Rust
2. **Provides flexibility** - Developers can choose clarity over dogma
3. **Maintains expression-oriented design** - `()` is the canonical form
4. **Supports explicit intent** - `pass` makes "doing nothing" clear

**Bottom line:** Both are valid. Use `()` for expression semantics, `pass` for clarity of no-op intent.

---

## References

- Implementation: `src/rust/parser/src/stmt_parsing/jump.rs`
- Spec Test: `test/system/features/control_flow/pass_unit_equivalence_spec.spl`
- Documentation: `doc/guide/syntax_quick_reference.md`
- Issue: (none - this is original design)
