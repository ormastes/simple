# Enumerate Shorthand Syntax

*Source: `simple/std_lib/test/features/control_flow/enumerate_shorthand_spec.spl`*

---

# Enumerate Shorthand Syntax

**Feature ID:** #53
**Category:** Control Flow
**Difficulty:** 1/5 (Beginner)
**Status:** Complete

## Overview

The enumerate shorthand provides a concise syntax for iterating over collections while also
tracking the index of each element. Instead of manually managing a counter variable or using
the `.enumerate()` method explicitly, you can use the shorthand `for i, item in items:` syntax.

**Design Philosophy:**
Tracking indices during iteration is a common need (80%+ of loops need indices at some point).
The shorthand syntax makes this pattern as easy as a regular for-in loop, following Python's
ergonomic design principles.

## Syntax

### Enumerate Shorthand

```simple
for index, item in collection:
    # index is 0-based integer
    # item is the element at that index
    print("{index}: {item}")
```

**Grammar:**
```
for_stmt = 'for' identifier ',' pattern 'in' expression ':' block
```

### Equivalent Explicit Form

```simple
for (index, item) in collection.enumerate():
    print("{index}: {item}")
```

## Runtime Representation

**Execution Flow:**
1. Evaluate collection expression
2. Wrap items with indices: `[(0, item0), (1, item1), ...]`
3. For each `(index, item)` tuple:
   - Bind index to first identifier
   - Bind item to second pattern
   - Execute loop body
4. Continue until collection exhausted

**Note:** The shorthand is syntactic sugar - it compiles to the same internal representation
as the explicit `.enumerate()` form.

## Comparison with Other Languages

| Feature | Simple | Python | Rust | Go | JavaScript |
|---------|--------|--------|------|-----|------------|
| Enumerate method | ✅ `.enumerate()` | ✅ `enumerate()` | ✅ `.enumerate()` | ✅ `range` returns index | ❌ Use `.forEach()` |
| Shorthand syntax | ✅ `for i, x in items:` | ✅ `for i, x in enumerate(items):` | ❌ Must use `.enumerate()` | ✅ `for i, v := range` | ❌ None |
| Index position | First | First | First | First | N/A |
| Zero-based | ✅ Yes | ✅ Yes | ✅ Yes | ✅ Yes | N/A |

## Common Patterns

### Basic Index Tracking

```simple
val fruits = ["apple", "banana", "cherry"]
for i, fruit in fruits:
    print("{i}: {fruit}")
# Output:
# 0: apple
# 1: banana
# 2: cherry
```

### Finding Element Position

```simple
val items = [10, 20, 30, 40, 50]
var found_index = -1
for i, item in items:
    if item == 30:
        found_index = i
        break
# found_index is 2
```

### Conditional Processing by Position

```simple
val rows = ["header", "data1", "data2", "data3"]
for i, row in rows:
    if i == 0:
        print("HEADER: {row}")
    else:
        print("  ROW {i}: {row}")
```

### Building Indexed Results

```simple
val words = ["hello", "world"]
var indexed = []
for i, word in words:
    indexed.push({index: i, value: word})
```

### Parallel Array Processing

```simple
val names = ["Alice", "Bob", "Charlie"]
val scores = [95, 87, 92]
for i, name in names:
    print("{name}: {scores[i]}")
```

### Last Element Detection

```simple
val items = [1, 2, 3, 4, 5]
val len = items.len()
for i, item in items:
    if i == len - 1:
        print("Last item: {item}")
    else:
        print("Item: {item}")
```

## Comparison with Explicit Enumerate

The shorthand is purely syntactic sugar. These are equivalent:

```simple
# Shorthand (recommended for readability)
for i, item in items:
    process(i, item)

# Explicit enumerate method
for (i, item) in items.enumerate():
    process(i, item)

# Manual index management (verbose, error-prone)
var i = 0
for item in items:
    process(i, item)
    i = i + 1
```

## Implementation Files

**Parser:** `src/parser/src/stmt_parsing/control_flow.rs:108-157` - parse_for_pattern()
**AST:** `src/parser/src/ast/nodes/statements.rs:98-99` - ForStmt.auto_enumerate flag
**Interpreter:** `src/compiler/src/interpreter_control.rs:517-522` - Auto-enumerate wrapping
**Tests:** `src/driver/tests/interpreter_control.rs` - Enumerate shorthand tests

## Related Features

- **Loops (#13):** Base for-in loop functionality
- **Collections (#45):** The `.enumerate()` method on collections
- **Tuples (#22):** Destructuring in patterns
- **Pattern Matching (#35):** Complex item patterns supported

## Limitations and Future Work

**Current Limitations:**
- Index is always first (can't do `for item, i in items:`)
- Can't specify starting index (always 0)

**Planned Features:**
- Starting index: `for i, item in items from 1:` (1-based indexing)
- Reverse iteration: `for i, item in items.reversed():`
- Step iteration: `for i, item in items by 2:`

## Enumerate Shorthand - Index Tracking Made Easy

    The enumerate shorthand `for i, item in items:` provides a concise way to
    iterate over a collection while also tracking the index of each element.
    This is syntactic sugar for the more verbose `.enumerate()` method call.

    **Key Properties:**
    - Index is always 0-based
    - Index variable comes first: `for index, item`
    - Works with any iterable (arrays, strings, ranges)
    - Item can be any pattern (identifier, tuple, etc.)

    **Grammar:**
    ```
    for_stmt = 'for' identifier ',' pattern 'in' expression ':' block
    ```

    **Implementation:** `src/parser/src/stmt_parsing/control_flow.rs:parse_for_pattern()`

**Given** a list of items
        **When** using enumerate shorthand
        **Then** both index and item are available in the loop body

        The most basic use case - iterate with both index and value.

**Given** a non-empty list
        **When** iterating with enumerate shorthand
        **Then** the first index is 0

        Simple uses 0-based indexing consistently.

**Given** an array of numbers
        **When** using enumerate shorthand
        **Then** can access both position and value

        Arrays are the most common use case for enumeration.

**Given** a string
        **When** iterating with enumerate shorthand
        **Then** get index and character

        Strings are iterable character-by-character.

**Given** an empty list
        **When** using enumerate shorthand
        **Then** loop body never executes

        Empty collections result in zero iterations.

## Advanced Pattern Usage with Enumerate

    The item portion of enumerate shorthand supports full pattern matching,
    allowing destructuring of complex elements.

**Given** a list of tuples
        **When** using tuple pattern in enumerate shorthand
        **Then** can destructure both index and tuple components

        Useful for processing structured data with position tracking.

## Shorthand vs Explicit Enumerate

    The shorthand syntax is purely syntactic sugar - it produces identical
    results to the explicit `.enumerate()` method call.

**Given** a list of items
        **When** using shorthand vs explicit enumerate
        **Then** both produce identical results

        Choose based on style preference - shorthand is more concise.

**Given** a loop with break
        **When** using enumerate shorthand
        **Then** break works as expected

        Control flow works identically to explicit enumerate.

**Given** a loop with continue
        **When** using enumerate shorthand
        **Then** continue skips to next iteration

        Continue advances both index and item together.
