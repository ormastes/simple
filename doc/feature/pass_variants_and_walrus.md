# Enhanced Pass Keywords & Walrus Operator

**Status:** Implemented (2026-02-13)
**Version:** 1.0.0

## Overview

This feature adds semantic distinctions for placeholder code and introduces the walrus operator (`:=`) as syntactic sugar for immutable declarations.

## Pass Variants

### Syntax

```simple
pass                              # Generic no-op (backward compatible)
pass("message")                   # With optional message

pass_todo                         # TODO marker
pass_todo("reason")              # With reason

pass_do_nothing                   # Intentional no-op
pass_do_nothing("explanation")   # With explanation

pass_dn                          # Alias for pass_do_nothing
pass_dn("context")               # With context
```

### Semantics

All pass variants:
- Evaluate to `nil`
- Are valid expressions and statements
- Compile to C comments (no runtime overhead)

| Variant | C Output | Use Case |
|---------|----------|----------|
| `pass` | `/* pass */` | Generic placeholder (discouraged in favor of specific variants) |
| `pass_todo` | `/* TODO */` or `/* TODO: message */` | Marks unimplemented code |
| `pass_do_nothing` | `/* intentional no-op */` or `/* no-op: message */` | Intentional empty implementation |
| `pass_dn` | Same as `pass_do_nothing` | Shorthand alias |

### Examples

```simple
fn not_yet_implemented():
    pass_todo("add validation logic")

fn default_handler():
    pass_do_nothing("extension point for plugins")

fn stub_for_testing():
    pass_dn
```

## Walrus Operator (`:=`)

### Syntax

```simple
x := value    # Equivalent to: val x = value
```

### Semantics

- Creates an **immutable binding** (same as `val`)
- Type is inferred from the right-hand side
- Only works at statement level (not in nested expressions)
- More concise than `val` for simple cases

### Examples

```simple
# Basic usage
count := 42
name := "Alice"
items := [1, 2, 3]

# With expressions
sum := 10 + 20 + 30
doubled := count * 2

# In functions
fn calculate():
    result := 100
    result * 2

# Equivalent to val
x := 5        # Same as: val x = 5
```

### Restrictions

- Cannot be used in expression contexts (only statements)
- Left side must be a simple identifier (no patterns)

**Invalid:**
```simple
# These won't work:
fn returns_walrus() := 42      # Syntax error
(x) := 5                       # Syntax error
if (y := compute()):           # Syntax error (use val instead)
```

## Implementation Status

### Core Implementation
- ✅ Token definitions (`TOK_KW_PASS_TODO`, `TOK_KW_PASS_DO_NOTHING`, `TOK_KW_PASS_DN`, `TOK_WALRUS`)
- ✅ Lexer support (`:=` tokenization)
- ✅ Parser support (pass variants with optional messages, walrus desugaring)
- ✅ AST nodes (`EXPR_PASS_TODO`, `EXPR_PASS_DO_NOTHING`, `EXPR_PASS_DN`)
- ✅ Interpreter support (all variants evaluate to nil)
- ✅ C codegen (appropriate comments for each variant)
- ✅ Seed compiler support (C-based bootstrap compiler)

### Testing
- ✅ SSpec tests (`test/feature/pass_variants_spec.spl`)
- ✅ SSpec tests (`test/feature/walrus_operator_spec.spl`)
- ⏳ Cross-platform seed tests (pending runtime rebuild)

### Documentation
- ✅ Feature documentation (this file)
- ⏳ Syntax quick reference update
- ⏳ CLAUDE.md update
- ⏳ MEMORY.md update

## Migration Guide

### From Plain `pass`

**Before:**
```simple
fn stub():
    pass  # What kind of placeholder is this?
```

**After:**
```simple
fn stub_unimplemented():
    pass_todo  # Clear: not implemented yet

fn stub_intentional():
    pass_do_nothing  # Clear: intentionally empty
```

### From `val` to `:=`

**Before:**
```simple
val count = 42
val name = "Alice"
val items = [1, 2, 3]
```

**After (optional):**
```simple
count := 42
name := "Alice"
items := [1, 2, 3]
```

**Note:** Both forms are equivalent. Use `:=` for conciseness or `val` for clarity.

## Technical Notes

### Parser Implementation

- **Pass variants:** Parsed in `parse_primary()` with optional message parameter
- **Walrus operator:** Parsed in `parse_assignment()`, treated as special assignment
- **Message extraction:** Messages stored in `expr_s_val` field of AST node

### Codegen Details

- Pass variants compile to C comments (zero runtime cost)
- Messages are embedded in comments for debugging
- Walrus creates `const` declaration in generated C code

### Seed Compiler (C)

- Text-based pattern matching for pass keywords
- Walrus detection via `strstr(trimmed, ":=")`
- Desugars walrus to `const auto name = value;`

## Future Work

- Warning system: Emit warnings for plain `pass` in compiled mode
- Enhanced parser: Proper lookahead for walrus in more contexts
- Lint integration: Suggest specific pass variants instead of generic `pass`

## References

- Implementation Plan: `/home/ormastes/.claude/plans/expressive-spinning-ember.md`
- Test Files: `test/feature/pass_variants_spec.spl`, `test/feature/walrus_operator_spec.spl`
- Core Modules: `src/compiler_core/{tokens,lexer,ast,parser}.spl`
- Codegen: `src/compiler_core/{interpreter/eval,compiler/c_codegen}.spl`
- Seed Compiler: `seed/seed.c`
