# SSpec Test Writing Guide

**Purpose:** Complete guide for writing SSpec tests with documentation generation.

---

## Overview

SSpec is Simple's BDD testing framework that:
- Generates documentation from tests
- Supports doctest examples embedded in code
- Produces markdown specs from test files

---

## Document Structure Template

### Standard SSpec File Format

```simple
"""
# Feature Name Specification

**Status:** Complete | In Progress | Draft
**Feature IDs:** #100-110
**Keywords:** keyword1, keyword2
**Topics:** category-name

## Overview

High-level description of the feature and its purpose.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Term1   | Definition  |
| Term2   | Definition  |

## Related Specifications

- [Types](types.md) - Type system details
- [Memory](memory.md) - Memory model

## Examples

Basic usage examples with doctest assertions.
"""

import std.spec

describe "FeatureName":
    """
    ## Feature Category

    Detailed description for this section.
    """

    context "when condition":
        """
        ### Scenario: Condition Description

        Explanation of this test scenario.
        """

        it "does expected behavior":
            # Test implementation
            expect actual to eq expected
```

---

## Doctest in Documentation

### Inline Doctest Format

Embed executable examples in docstrings:

```simple
"""
## Stack Operations

A stack follows LIFO (Last In, First Out) ordering.

### Creating a Stack

>>> stack = Stack.new()
>>> stack.is_empty()
True

### Push and Pop

>>> stack = Stack.new()
>>> stack.push(1)
>>> stack.push(2)
>>> stack.pop()
2
>>> stack.pop()
1

### Peek Without Removal

>>> stack = Stack.new()
>>> stack.push(42)
>>> stack.peek()
42
>>> stack.is_empty()
False
"""
```

### Doctest Markers

| Marker | Purpose | Example |
|--------|---------|---------|
| `>>>` | Code to execute | `>>> 1 + 1` |
| (next line) | Expected output | `2` |
| `...` | Continuation | `... + 3` |
| `# doctest: +SKIP` | Skip this example | `>>> dangerous() # doctest: +SKIP` |
| `# doctest: +ELLIPSIS` | Allow `...` in output | `>>> long_output() # doctest: +ELLIPSIS` |

### Multi-line Expected Output

```simple
"""
>>> print_list([1, 2, 3])
[
  1,
  2,
  3
]
"""
```

### Expected Exceptions

```simple
"""
>>> divide(1, 0)
Traceback:
DivisionError: cannot divide by zero
"""
```

---

## Class Documentation with Doctest

### Complete Class Example

```simple
## Stack Data Structure
#
# A generic stack implementation with LIFO semantics.
#
# ## Usage
#
# >>> stack = Stack[Int].new()
# >>> stack.push(10)
# >>> stack.push(20)
# >>> stack.pop()
# 20
#
# ## Thread Safety
#
# This implementation is NOT thread-safe. Use `SyncStack` for concurrent access.
#
# ## Complexity
#
# | Operation | Time | Space |
# |-----------|------|-------|
# | push      | O(1) | O(1)  |
# | pop       | O(1) | O(1)  |
# | peek      | O(1) | O(1)  |
class Stack[T]:
    items: List[T]

    ## Create an empty stack.
    #
    # >>> Stack[Int].new().is_empty()
    # True
    fn new() -> Stack[T]:
        Stack { items: [] }

    ## Push an item onto the stack.
    #
    # >>> s = Stack[Int].new()
    # >>> s.push(42)
    # >>> s.peek()
    # 42
    fn push(mut self, item: T):
        self.items.append(item)

    ## Pop and return the top item.
    #
    # >>> s = Stack[Int].new()
    # >>> s.push(1)
    # >>> s.push(2)
    # >>> s.pop()
    # 2
    #
    # @raises EmptyStackError - If stack is empty
    fn pop(mut self) -> T:
        if self.is_empty():
            raise EmptyStackError("cannot pop from empty stack")
        self.items.pop()

    ## Peek at the top item without removing it.
    #
    # >>> s = Stack[Int].new()
    # >>> s.push(99)
    # >>> s.peek()
    # 99
    # >>> s.is_empty()
    # False
    fn peek(self) -> T:
        if self.is_empty():
            raise EmptyStackError("cannot peek empty stack")
        self.items[self.items.len() - 1]

    ## Check if the stack is empty.
    #
    # >>> Stack[Int].new().is_empty()
    # True
    # >>> s = Stack[Int].new()
    # >>> s.push(1)
    # >>> s.is_empty()
    # False
    fn is_empty(self) -> Bool:
        self.items.len() == 0
```

---

## Function Documentation with Doctest

### Complete Function Example

```simple
## Calculate factorial of a non-negative integer.
#
# The factorial of n (written n!) is the product of all positive
# integers less than or equal to n.
#
# ## Examples
#
# >>> factorial(0)
# 1
# >>> factorial(1)
# 1
# >>> factorial(5)
# 120
# >>> factorial(10)
# 3628800
#
# ## Edge Cases
#
# >>> factorial(-1)
# Traceback:
# ValueError: factorial requires non-negative integer
#
# @param n - Non-negative integer
# @returns n! (n factorial)
# @raises ValueError - If n is negative
# @complexity O(n) time, O(1) space
fn factorial(n: Int) -> Int:
    in: n >= 0, "factorial requires non-negative integer"
    out(ret): ret >= 1

    if n <= 1:
        1
    else:
        n * factorial(n - 1)
```

---

## SSpec Test Structure

### Describe Blocks

```simple
describe "ClassName":
    """
    # ClassName Specification

    Overview of the class being tested.
    """

    # Tests go here
```

### Context Blocks

```simple
describe "Stack":
    context "when empty":
        """
        ### Empty Stack Behavior

        An empty stack has specific behavior for all operations.
        """

        it "returns true for is_empty":
            stack = Stack.new()
            expect stack.is_empty() to be true

        it "raises error on pop":
            stack = Stack.new()
            expect_raises EmptyStackError:
                stack.pop()

    context "with items":
        """
        ### Non-Empty Stack Behavior
        """

        before_each:
            @stack = Stack.new()
            @stack.push(1)
            @stack.push(2)

        it "returns false for is_empty":
            expect @stack.is_empty() to be false

        it "pops in LIFO order":
            expect @stack.pop() to eq 2
            expect @stack.pop() to eq 1
```

### Fixtures

```simple
describe "UserService":
    # Lazy fixture - created on first access
    given_lazy :user, \:
        User { name: "Alice", age: 30 }

    # Eager fixture - created in before_each
    given :db_conn, \:
        Database.connect("test")

    it "creates user":
        expect user.name to eq "Alice"
```

### Shared Contexts

```simple
# Define reusable context
context_def :authenticated_user:
    given_lazy :user, \:
        User.create(role: "admin")

    given_lazy :token, \:
        Auth.generate_token(user)

describe "AdminDashboard":
    # Include shared context
    context :authenticated_user:
        it "shows admin panel":
            expect user.role to eq "admin"
```

---

## Matchers Reference

### Equality

```simple
expect value to eq expected        # Equal
expect value to be expected        # Same reference
expect value to be_nil             # Is None/nil
expect value not_to eq other       # Not equal
```

### Comparison

```simple
expect 10 to gt 5                  # Greater than
expect 5 to lt 10                  # Less than
expect 10 to gte 10                # Greater or equal
expect 5 to lte 10                 # Less or equal
expect 5 to be_between 1, 10       # In range
```

### Collections

```simple
expect [1, 2, 3] to include 2      # Contains item
expect [1, 2, 3] to have_length 3  # Length check
expect [] to be_empty              # Empty collection
expect [1, 2] to contain_exactly [1, 2]  # Exact match
expect [1, 2, 3] to start_with [1, 2]    # Starts with
```

### Strings

```simple
expect "hello" to include_string "ell"
expect "hello" to start_with "hel"
expect "hello" to end_with "lo"
expect "hello" to match_regex r"h.*o"
expect "" to be_blank
```

### Types

```simple
expect value to be_a SomeType
expect value to respond_to "method_name"
```

### Errors

```simple
expect_raises ValueError:
    raise ValueError("bad")

expect_raises:
    risky_operation()

expect { risky() } to raise_error ValueError
```

---

## Generated Document Format

### Spec File → Markdown Output

**Input:** `stack_spec.spl`
```simple
"""
# Stack Specification

**Status:** Complete
**Feature IDs:** #20-25

## Overview

Stack data structure implementation.
"""

describe "Stack":
    """
    ## Core Operations
    """

    context "push and pop":
        """
        ### LIFO Semantics

        >>> s = Stack.new()
        >>> s.push(1); s.push(2)
        >>> s.pop()
        2
        """

        it "follows LIFO order":
            s = Stack.new()
            s.push(1)
            s.push(2)
            expect s.pop() to eq 2
```

**Output:** `doc/spec/generated/stack.md`
```markdown
# Stack Specification

**Status:** Complete
**Feature IDs:** #20-25

## Overview

Stack data structure implementation.

## Core Operations

### LIFO Semantics

```simple
>>> s = Stack.new()
>>> s.push(1); s.push(2)
>>> s.pop()
2
```

#### Test: follows LIFO order

```simple
s = Stack.new()
s.push(1)
s.push(2)
expect s.pop() to eq 2
```

**Result:** PASS
```

---

## File Organization

### Test Directory Structure

```
simple/std_lib/test/
├── unit/                      # Fast, isolated tests
│   ├── core/
│   │   ├── stack_spec.spl
│   │   └── queue_spec.spl
│   └── utils/
│       └── string_spec.spl
├── integration/               # Cross-module tests
│   └── http/
│       └── client_spec.spl
└── system/                    # Full system tests
    └── e2e/
        └── workflow_spec.spl
```

### Naming Conventions

| Type | Pattern | Example |
|------|---------|---------|
| Spec file | `*_spec.spl` | `stack_spec.spl` |
| Test file | `*_test.spl` | `stack_test.spl` |
| Describe | `"ClassName"` | `"Stack"` |
| Context | `"when ..."` | `"when empty"` |
| It | `"does ..."` | `"returns nil"` |

---

## Running Tests

### Commands

```bash
# All tests
cargo test -p simple-driver simple_stdlib

# By layer
cargo test -p simple-driver simple_stdlib_unit
cargo test -p simple-driver simple_stdlib_integration
cargo test -p simple-driver simple_stdlib_system

# Specific test
./target/debug/simple simple/std_lib/test/unit/core/stack_spec.spl

# With options
simple test --tag slow
simple test --fail-fast
simple test --match "Stack when empty"
```

### Generate Documentation

```bash
# Generate specs from test files
cargo run --bin gen-sspec-docs -- tests/specs/*.spl

# Output to specific directory
cargo run --bin gen-sspec-docs -- tests/specs/*.spl --output doc/spec/generated/
```

---

## Best Practices

### 1. One Assertion Per Test

```simple
# Good
it "returns correct length":
    expect [1, 2, 3].len() to eq 3

it "is not empty":
    expect [1, 2, 3].is_empty() to be false

# Avoid
it "works correctly":
    expect [1, 2, 3].len() to eq 3
    expect [1, 2, 3].is_empty() to be false
    expect [1, 2, 3][0] to eq 1
```

### 2. Descriptive Names

```simple
# Good
it "raises ValueError when divisor is zero":
it "returns empty list when input is empty":

# Avoid
it "works":
it "handles edge case":
```

### 3. Doctest for Documentation

Use doctest in:
- Class/struct documentation
- Function documentation
- Module overview

```simple
## Convert string to uppercase.
#
# >>> to_upper("hello")
# "HELLO"
# >>> to_upper("Hello World")
# "HELLO WORLD"
fn to_upper(s: String) -> String:
    s.to_uppercase()
```

### 4. Keep Tests Fast

```simple
# Unit tests should be < 100ms
# Use mocks for external dependencies
describe "HttpClient":
    given :client, \:
        MockHttpClient.new()

    it "sends request":
        expect @client.get("/api").status to eq 200
```

### 5. Complete Document Header

Always include metadata in spec docstrings:

```simple
"""
# Feature Name

**Status:** Complete | In Progress | Draft
**Feature IDs:** #XXX-XXX
**Keywords:** keyword1, keyword2
**Topics:** category-name

## Overview
...
"""
```

---

## Sample Complete Spec

```simple
"""
# Queue Specification

**Status:** Complete
**Feature IDs:** #30-35
**Keywords:** queue, fifo, data-structure
**Topics:** data-structures

## Overview

A queue is a FIFO (First In, First Out) data structure.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Enqueue | Add item to back |
| Dequeue | Remove item from front |
| Peek    | View front item |

## Related Specifications

- [Stack](stack.md) - LIFO counterpart
- [Deque](deque.md) - Double-ended queue
"""

import std.spec

describe "Queue":
    """
    ## Queue[T] Implementation

    Generic queue supporting any element type.
    """

    context "when empty":
        """
        ### Empty Queue Behavior

        >>> q = Queue[Int].new()
        >>> q.is_empty()
        True
        >>> q.len()
        0
        """

        it "is_empty returns true":
            q = Queue[Int].new()
            expect q.is_empty() to be true

        it "has length zero":
            q = Queue[Int].new()
            expect q.len() to eq 0

        it "raises on dequeue":
            q = Queue[Int].new()
            expect_raises EmptyQueueError:
                q.dequeue()

    context "with items":
        """
        ### Non-Empty Queue Operations

        >>> q = Queue[Int].new()
        >>> q.enqueue(1)
        >>> q.enqueue(2)
        >>> q.dequeue()
        1
        >>> q.dequeue()
        2
        """

        before_each:
            @queue = Queue[Int].new()
            @queue.enqueue(10)
            @queue.enqueue(20)
            @queue.enqueue(30)

        it "is_empty returns false":
            expect @queue.is_empty() to be false

        it "has correct length":
            expect @queue.len() to eq 3

        it "dequeues in FIFO order":
            expect @queue.dequeue() to eq 10
            expect @queue.dequeue() to eq 20
            expect @queue.dequeue() to eq 30

        it "peek returns front without removal":
            expect @queue.peek() to eq 10
            expect @queue.len() to eq 3

    context "edge cases":
        """
        ### Edge Case Handling
        """

        it "handles single item":
            q = Queue[String].new()
            q.enqueue("only")
            expect q.dequeue() to eq "only"
            expect q.is_empty() to be true

        it "handles interleaved operations":
            q = Queue[Int].new()
            q.enqueue(1)
            q.enqueue(2)
            expect q.dequeue() to eq 1
            q.enqueue(3)
            expect q.dequeue() to eq 2
            expect q.dequeue() to eq 3
```

---

## See Also

- [coding_style.md](coding_style.md) - Coding conventions with doctest
- [test.md](test.md) - Test policy and coverage
- [sspec skill](/.claude/skills/sspec.md) - Quick reference
- [doc/spec/doctest_readme.md](../spec/doctest_readme.md) - README-based doctest spec
