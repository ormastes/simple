# Error Recovery System Guide

**Status:** Production-ready (v1.0)
**Last Updated:** 2026-01-12

## Overview

The Simple language compiler includes an intelligent error recovery system that detects common syntax mistakes from other programming languages and provides helpful, contextual suggestions. This makes it easier for developers to transition to Simple from Python, Rust, Java, C++, TypeScript, and other languages.

## How It Works

The error recovery system operates during parsing:

1. **Token-Level Detection**: As the parser advances through tokens, it checks for common mistake patterns
2. **Context-Aware Analysis**: Uses previous, current, and next tokens to identify patterns
3. **Hint Generation**: Creates helpful error messages with:
   - Severity level (Error, Warning, Info, Hint)
   - Line and column location
   - Source code snippet with caret pointer
   - Suggested fix
   - Side-by-side examples (wrong vs. correct)
4. **Early Display**: Hints appear before semantic analysis, giving immediate feedback

## Detected Patterns

### Python Mistakes

#### `def` keyword
**Detects:** `def function_name():`
**Suggests:** Use `fn function_name():`
**Level:** Error

```simple
# Wrong (Python)
def add(a, b):
    return a + b

# Correct (Simple)
fn add(a, b):
    return a + b
```

#### `None` literal
**Detects:** `None`
**Suggests:** Use `nil`
**Level:** Error

```simple
# Wrong (Python)
val result = None

# Correct (Simple)
val result = nil
```

#### `True` / `False` literals
**Detects:** `True`, `False`
**Suggests:** Use lowercase `true`, `false`
**Level:** Error

```simple
# Wrong (Python)
val is_ready = True
val is_done = False

# Correct (Simple)
val is_ready = true
val is_done = false
```

#### Explicit `self.` field access
**Detects:** `self.field_name`
**Suggests:** Use implicit `self` - just `field_name`
**Level:** Info

```simple
# Verbose (Python-style)
impl MyStruct:
    fn update():
        self.value = 10  # Hint: self is implicit

# Idiomatic (Simple)
impl MyStruct:
    fn update():
        value = 10  # self is implicit in methods
```

### Rust Mistakes

#### `let mut` variable declaration
**Detects:** `let mut variable_name`
**Suggests:** Use `var variable_name`
**Level:** Error

```simple
# Wrong (Rust)
let mut counter = 0

# Correct (Simple)
var counter = 0
```

#### Turbofish syntax
**Detects:** `::<Type>`
**Suggests:** Simple doesn't need turbofish
**Level:** Hint

```simple
# Wrong (Rust)
val result = collect::<Vec<i32>>()

# Correct (Simple)
val result = collect()  # Type inference works
```

#### Macro syntax
**Detects:** `identifier!`
**Suggests:** Use `@macro` syntax
**Level:** Hint

```simple
# Wrong (Rust)
println!("Hello, world!")

# Correct (Simple)
@println("Hello, world!")
```

### Java/C++ Mistakes

#### `public class` declaration
**Detects:** `public class ClassName`
**Suggests:** Use `pub class` or `pub struct`
**Level:** Error

```simple
# Wrong (Java)
public class Point { }

# Correct (Simple)
pub struct Point:
    x: i32
    y: i32
```

#### `void` return type
**Detects:** `void` keyword
**Suggests:** Omit return type for void functions
**Level:** Error

```simple
# Wrong (Java/C++)
void print_message():
    print("Hello")

# Correct (Simple)
fn print_message():
    print("Hello")  # No return type needed
```

#### `new` keyword
**Detects:** `new TypeName()`
**Suggests:** Use struct literal syntax
**Level:** Error

```simple
# Wrong (Java/C++)
val point = new Point(1, 2)

# Correct (Simple)
val point = Point { x: 1, y: 2 }
```

#### `this` keyword
**Detects:** `this` as identifier
**Suggests:** Use `self` (which is implicit in methods)
**Level:** Error

```simple
# Wrong (Java/JavaScript)
val instance = this

# Correct (Simple)
# In methods, self is implicit - just use field names directly
```

#### `namespace` keyword
**Detects:** `namespace` as identifier
**Suggests:** Use `mod` for modules
**Level:** Error

```simple
# Wrong (C++)
namespace math:
    fn square(x):
        return x * x

# Correct (Simple)
mod math:
    fn square(x):
        return x * x
```

#### `template` keyword
**Detects:** `template` as identifier
**Suggests:** Generic parameters come after the name
**Level:** Error

```simple
# Wrong (C++)
template<typename T> class Vec { }

# Correct (Simple)
struct Vec<T>:
    items: List<T>
```

### TypeScript/JavaScript Mistakes

#### `function` keyword
**Detects:** `function function_name()`
**Suggests:** Use `fn function_name()`
**Level:** Error

```simple
# Wrong (TypeScript)
function add(a, b):
    return a + b

# Correct (Simple)
fn add(a, b):
    return a + b
```

#### `const` variable
**Detects:** `const` as identifier (when used like TypeScript)
**Suggests:** Use `val` for immutable variables
**Level:** Error

```simple
# Wrong (TypeScript)
const MAX_SIZE = 100

# Correct (Simple)
val MAX_SIZE = 100
```

#### `let` variable
**Detects:** `let` keyword
**Suggests:** Use `val` (immutable) or `var` (mutable)
**Level:** Info

```simple
# Discouraged (TypeScript)
let counter = 0

# Preferred (Simple)
val x = 5      # Immutable (preferred)
var counter = 0  # Mutable (when needed)
```

#### `interface` keyword
**Detects:** `interface` as identifier
**Suggests:** Use `trait` instead
**Level:** Error

```simple
# Wrong (TypeScript)
interface Named:
    name: String

# Correct (Simple)
trait Named:
    name: String
```

#### Arrow function syntax
**Detects:** `) =>`
**Suggests:** Use `:` for functions, `=>` for lambdas only
**Level:** Hint

```simple
# Wrong (TypeScript function)
fn add(a, b) => a + b

# Correct (Simple function)
fn add(a, b):
    return a + b

# Correct (Simple lambda)
val add = \a, b: a + b
```

### Generic Mistakes

#### Wrong brackets for generics
**Detects:** `Type[Generic]`
**Suggests:** Use angle brackets `Type<Generic>`
**Level:** Warning

```simple
# Wrong
val items = List[String]

# Correct
val items = List<String>
```

## Error Hint Levels

The system uses four severity levels:

1. **Error** (Red): Wrong syntax that won't work
   - Python `def`, `None`, `True`, `False`
   - TypeScript `function`, `const`
   - Java/C++ `void`, `new`, `this`

2. **Warning** (Yellow): Valid but non-idiomatic
   - Wrong brackets `[T]` instead of `<T>`

3. **Info** (Cyan): Style suggestions
   - TypeScript `let` (suggest `val`/`var`)
   - Python `self.x` (self is implicit)

4. **Hint** (Green): Advanced patterns
   - Rust turbofish `::<T>`
   - Rust macros `identifier!`
   - TypeScript arrow functions `=>`

## Example Output

When you write code with common mistakes:

```simple
# test.spl
def calculate(x):
    val result = None
    val flag = True
    return result
```

The compiler displays:

```
error: Common mistake detected: Replace 'def' with 'fn'
  --> line 1:1
   |
 1 | def calculate(x):
   | ^

Suggestion: Replace 'def' with 'fn'

Help:
Use 'fn' to define functions in Simple, not 'def'.

Python:  def add(a, b):
Simple:  fn add(a, b):

error: Common mistake detected: Replace 'None' with 'nil'
  --> line 2:17
   |
 2 |     val result = None
   |                  ^

Suggestion: Replace 'None' with 'nil'

Help:
Use 'nil' instead of 'None' in Simple.

Python:  return None
Simple:  return nil
```

## Implementation Details

### Architecture

- **Module**: `src/parser/src/error_recovery.rs`
- **Detection**: `detect_common_mistake()` function
- **Integration**: Parser's `advance()` method
- **Display**: Driver's `display_error_hints()` method

### Pattern Detection

Patterns are detected by analyzing token sequences:

```rust
pub fn detect_common_mistake(
    current: &Token,
    previous: &Token,
    next: Option<&Token>,
) -> Option<CommonMistake>
```

Each pattern checks:
- Current token type and lexeme
- Previous token context
- Next token (lookahead)

### Adding New Patterns

To add a new mistake pattern:

1. Add variant to `CommonMistake` enum
2. Implement `message()` and `suggestion()` methods
3. Add detection logic in `detect_common_mistake()`
4. Set severity level in parser_helpers.rs
5. Add unit test in `tests/error_recovery_test.rs`

## Coverage Statistics

**Total Patterns Detected:** 19
- Python: 4 patterns
- Rust: 3 patterns
- Java/C++: 6 patterns
- TypeScript/JS: 5 patterns
- Generic: 1 pattern

**Test Coverage:**
- 15 unit tests in error_recovery_test.rs
- All tests passing
- End-to-end integration verified

## Future Enhancements

Patterns defined but not yet actively detected:

1. **Explicit `self` parameter** - Detect `(self)` in method signatures
2. **Verbose return types** - Detect unnecessary return type annotations
3. **Unnecessary semicolons** - Detect C-style semicolons
4. **Missing colons** - Detect missing `:` before blocks
5. **Semicolons after blocks** - Detect `};` instead of `}`

These patterns require more sophisticated context or would produce too many false positives in current form.

## See Also

- [Common Mistakes Guide](common_mistakes.md) - User-facing quick reference
- [Error Messages Demo](../examples/error_messages_demo.spl) - Interactive examples
- [Coding Skill](.claude/skills/coding.md) - Development reference

## References

- Error Recovery Module: `src/parser/src/error_recovery.rs`
- Parser Integration: `src/parser/src/parser_helpers.rs`
- Driver Display: `src/driver/src/exec_core.rs`
- Tests: `src/parser/tests/error_recovery_test.rs`
