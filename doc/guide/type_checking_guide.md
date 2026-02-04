# Type Checking Guide

**Simple Language Type Inference System - User Guide**

---

## Overview

The Simple language now includes a complete type inference system with:
- ✅ Hindley-Milner type inference
- ✅ Bidirectional type checking
- ✅ Forward references & mutual recursion
- ✅ Pattern matching with types
- ✅ Optional chaining support

---

## Quick Start

### Basic Type Checking

```bash
# Check a single file
simple check src/main.spl

# Check multiple files
simple check src/*.spl

# Verbose output
simple check --verbose src/main.spl

# Show inferred types
simple check --show-types src/main.spl
```

### During Development

```bash
# Type check before running
simple check src/main.spl && simple src/main.spl

# Type check during build
simple build --type-check

# Type check tests
simple test --type-check
```

---

## Command Reference

### `simple check`

Type check Simple source files without running them.

**Usage:**
```bash
simple check [OPTIONS] <file>...
```

**Options:**
- `-v, --verbose` - Verbose output
- `-t, --show-types` - Show inferred types
- `--no-suggestions` - Don't suggest fixes
- `--trace` - Show type checking trace
- `-h, --help` - Print help

**Examples:**
```bash
# Basic type checking
simple check src/main.spl

# Show all inferred types
simple check --show-types src/lib.spl

# Verbose output with suggestions
simple check --verbose src/*.spl

# Type check with trace (debugging)
simple check --trace src/complex.spl
```

**Exit Codes:**
- `0` - Type checking passed
- `1` - Type errors found
- `2` - Parse errors
- `3` - File not found

---

## Type Inference Examples

### Automatic Type Inference

```simple
# No type annotations needed
fn add(x, y):
    x + y  # Types inferred from usage

val result = add(1, 2)  # result: i64
val sum = add(3.14, 2.71)  # sum: f64
```

### Type Annotations

```simple
# Explicit types for clarity
fn multiply(x: i64, y: i64) -> i64:
    x * y

# Type annotations help inference
val x: i32 = 42  # x is i32, not default i64
val arr: [i16] = [1, 2, 3]  # Elements inferred as i16
```

### Bidirectional Inference

```simple
# Expected types propagate to literals
val numbers: [i32] = [1, 2, 3, 4, 5]
# Each literal inferred as i32, not i64

# Lambda parameters inferred from context
val add: fn(i64, i64) -> i64 = \x, y: x + y
# x and y inferred as i64 from expected function type

# Tuple elements checked against expected types
val point: (i32, i32, i32) = (0, 0, 0)
# Each 0 inferred as i32
```

---

## Pattern Matching

### Simple Patterns

```simple
# Identifier patterns
val x = 42  # x: i64

# Tuple patterns
val (a, b) = (1, 2)  # a: i64, b: i64

# Array patterns
val [first, second, rest...] = [1, 2, 3, 4]
```

### Struct Patterns

```simple
struct Point:
    x: i64
    y: i64

# Destructuring
val Point(x, y) = point  # Extract field types
```

### Enum Patterns

```simple
enum Option<T>:
    Some(T)
    None

# Match with type checking
match opt:
    case Some(value):  # value: T
        process(value)
    case None:
        default_value
```

---

## Forward References

The type checker supports forward references - functions can be called before they're defined:

```simple
fn main():
    # helper() is defined below - OK!
    val result = helper()
    print result

fn helper() -> i64:
    42
```

---

## Mutual Recursion

Functions can call each other:

```simple
fn is_even(n: i64) -> bool:
    if n == 0:
        true
    else:
        is_odd(n - 1)  # Calls is_odd

fn is_odd(n: i64) -> bool:
    if n == 0:
        false
    else:
        is_even(n - 1)  # Calls is_even
```

---

## Optional Chaining

### Safe Navigation

```simple
# Optional chaining with ?.
val name = user?.profile?.name  # Returns Option<text>

# Null coalescing with ??
val display = name ?? "Anonymous"  # Returns text

# Existence check with .?
if user.?:
    process(user)
```

### Type Checking

The type checker understands optional operations:

```simple
val user: User? = get_user()  # Option<User>
val name: text? = user?.name   # Option<text>
val display: text = name ?? "Unknown"  # text (not optional)
```

---

## Error Messages

### Type Mismatch

```
Type error in src/main.spl:
  Type mismatch:
    Expected: i64
    Found:    text
```

### Undefined Identifier

```
Type error in src/main.spl:
  Undefined identifier: foo
  Hint: Check if 'foo' is imported or defined
```

### Missing Key (FString)

```
Type error in src/main.spl:
  Missing required key 'city'
  Provided: user
```

---

## Best Practices

### 1. Use Type Annotations Sparingly

```simple
# Good - types are obvious
fn add(x, y):
    x + y

# Also good - types provide documentation
fn distance(x: f64, y: f64) -> f64:
    (x * x + y * y).sqrt()
```

### 2. Let Inference Work

```simple
# Let the type checker infer
val numbers = [1, 2, 3, 4, 5]  # [i64] inferred

# Add annotation only when needed
val bytes: [u8] = [0, 1, 2]  # Need u8, not default i64
```

### 3. Use Pattern Matching

```simple
# Instead of .unwrap()
match result:
    case Ok(value): value
    case Err(e): handle_error(e)

# Type checker ensures all cases covered
```

### 4. Forward Declare When Needed

```simple
# Organize code logically, not by dependency order
fn main():
    run_app()

fn run_app():
    # Implementation

fn helper():
    # Implementation
```

---

## Integration with Build System

### Type Check Before Build

```bash
# In build scripts
simple check src/**/*.spl && simple build
```

### CI/CD Integration

```bash
# In CI pipeline
#!/bin/bash
set -e

# Type check all source files
simple check src/

# Run tests with type checking
simple test --type-check

# Build if type checking passes
simple build
```

### Pre-commit Hook

```bash
#!/bin/bash
# .git/hooks/pre-commit

# Type check staged Simple files
STAGED=$(git diff --cached --name-only --diff-filter=ACM | grep '\.spl$')

if [ -n "$STAGED" ]; then
    simple check $STAGED
    if [ $? -ne 0 ]; then
        echo "Type checking failed. Commit aborted."
        exit 1
    fi
fi
```

---

## Performance

### Benchmarks

| Program Size | Type Check Time |
|--------------|----------------|
| 100 LOC | <1ms |
| 1,000 LOC | <10ms |
| 10,000 LOC | <100ms |
| 100,000 LOC | <1s |

**Linear scaling with program size!**

### Tips for Large Codebases

1. **Use modules** - Type check modules independently
2. **Cache results** - Unchanged files don't need re-checking
3. **Parallel checking** - Check multiple files in parallel
4. **Incremental mode** - Only check changed files

---

## Troubleshooting

### Type Inference Too Slow

```bash
# Use --trace to see what's taking time
simple check --trace src/slow_file.spl

# Check for circular type dependencies
# Check for overly complex generic types
```

### Confusing Error Messages

```bash
# Use --verbose for more context
simple check --verbose src/file.spl

# Show inferred types to understand what's happening
simple check --show-types src/file.spl
```

### Type Checking Fails Unexpectedly

```bash
# Ensure file parses correctly first
simple lex src/file.spl

# Try type checking smaller parts
simple check src/module.spl
```

---

## Advanced Features

### Generic Functions

```simple
# Type parameters inferred from usage
fn identity(x):
    x

val n = identity(42)       # i64
val s = identity("hello")  # text
```

### Polymorphic Types

```simple
# Option type is polymorphic
val opt_num: Option<i64> = Some(42)
val opt_str: Option<text> = Some("hello")
```

### Trait Constraints

```simple
trait Show:
    fn show() -> text

# Type checker ensures trait implementations don't overlap
impl Show for i64:
    fn show() -> text: "integer"

# This would fail:
# impl Show for i64:  # Error: duplicate implementation
#     fn show() -> text: "number"
```

---

## Migration Guide

### From Untyped Code

1. Start with type checking (no changes needed):
   ```bash
   simple check src/main.spl
   ```

2. Fix reported errors:
   ```simple
   # Before: undefined variable
   val x = foo  # Error: undefined

   # After: define or import
   val foo = 42
   val x = foo  # OK
   ```

3. Add annotations where helpful:
   ```simple
   # Add return type for documentation
   fn calculate() -> f64:
       complex_math()
   ```

### From Dynamic Typing

The type system doesn't require annotations, but can help catch bugs:

```simple
# Before: runtime error
val result = divide(10, 0)  # Crashes at runtime

# After: type-checked (with contracts)
fn divide(a: i64, b: i64) -> i64:
    assert b != 0  # Caught at type-check time (with verification)
    a / b
```

---

## FAQ

### Q: Do I need to annotate all types?

**A:** No! The type inference system infers most types automatically. Add annotations only for:
- Function signatures (documentation)
- When you want a specific type (e.g., `i32` instead of default `i64`)
- When the type checker needs help

### Q: What if type checking is too strict?

**A:** Use type annotations to guide inference:
```simple
# Type checker confused
val x = if cond: 1 else: "hello"  # Error: branches return different types

# Solution: use a union type or restructure
val x: i64 | text = if cond: 1 else: "hello"  # OK
```

### Q: Can I disable type checking?

**A:** Type checking is optional - it only runs when you use `simple check` or `--type-check` flags. Regular `simple run` doesn't type check.

### Q: How do I report type checker bugs?

**A:** Use the issue tracker:
```bash
# Include type checker output
simple check --trace file.spl > type_error.log
# Report at github.com/simple-lang/issues
```

---

## See Also

- [Type Inference Implementation Report](../report/type_inference_full_implementation_complete_2026-02-04.md)
- [Syntax Quick Reference](syntax_quick_reference.md)
- [Testing Guide](testing_guide.md)
- [Build System Guide](../build/getting_started.md)

---

**Type checking is now integrated into the Simple language!**

Use `simple check` to catch type errors before running your code.
