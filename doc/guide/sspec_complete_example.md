# SSpec Complete Example: From Spec to Documentation

This guide demonstrates the complete workflow of writing an SSpec test and generating documentation.

## Scenario

We'll create a specification for a hypothetical "Pipeline Operators" feature in Simple.

## Step 1: Create Spec File

```bash
# Create directory
mkdir -p simple/test/system/features/pipeline_operators

# Copy template
cp .claude/templates/sspec_template.spl \
   simple/test/system/features/pipeline_operators/pipeline_operators_spec.spl
```

## Step 2: Write Module-Level Documentation

Edit `pipeline_operators_spec.spl`:

```simple
"""
# Pipeline Operators Specification

**Feature IDs:** #450-455
**Category:** Language
**Difficulty:** 3/5
**Status:** Implemented

## Overview

Pipeline operators enable functional composition by passing the result of one
expression as input to the next. This improves readability of nested function
calls and supports method chaining.

## Syntax

```simple
# Forward pipeline (|>)
val result = value
    |> transform1
    |> transform2
    |> finalStep

# Backward pipeline (<|)
val result = finalStep <| transform2 <| transform1 <| value
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Forward Pipeline | Passes result left-to-right (like Unix pipes) |
| Backward Pipeline | Passes result right-to-left (function application) |
| Partial Application | Pipelines work with partially applied functions |

## Behavior

- Pipeline operators have low precedence (evaluated after arithmetic)
- Type inference flows through the pipeline
- Supports both functions and method calls
- Can be chained indefinitely

## Related Specifications

- [Functions](functions.md) - Function application and currying
- [Type Inference](type_inference.md) - Type flow through pipelines
- [Operators](operators.md) - Operator precedence

## Implementation Notes

The pipeline operator desugars at the AST level:
- `x |> f` → `f(x)`
- `x |> f(y)` → `f(y, x)`  (partial application)

Performance: Zero runtime overhead - purely syntactic sugar.

## Examples

```simple
# Data transformation pipeline
val users = load_users()
    |> filter(is_active)
    |> map(to_display_name)
    |> sort_by(last_login)

# Mathematical operations
val result = 10
    |> add(5)
    |> multiply(2)
    |> divide(3)
```
"""

import std.spec


# ============================================================================
# Basic Pipeline Operations
# ============================================================================

describe "Pipeline Operators - Basic":
    """
    ## Basic Forward Pipeline

    The forward pipeline `|>` passes a value to the next function.
    """

    context "with simple functions":
        """
        ### Scenario: Single Function Application

        Applying one function to a value using the pipeline operator.

        ```simple
        val result = 5 |> double
        # Equivalent to: double(5)
        ```
        """

        it "applies function to value":
            fn double(x: Int) -> Int:
                x * 2

            val result = 5 |> double
            expect(result).to(eq(10))

    context "with chained operations":
        """
        ### Scenario: Multiple Pipeline Steps

        Chaining multiple transformations in sequence.

        ```simple
        val result = 5 |> double |> add_one |> triple
        # Equivalent to: triple(add_one(double(5)))
        ```
        """

        it "chains multiple operations":
            fn double(x: Int) -> Int:
                x * 2

            fn add_one(x: Int) -> Int:
                x + 1

            fn triple(x: Int) -> Int:
                x * 3

            val result = 5
                |> double    # 10
                |> add_one   # 11
                |> triple    # 33

            expect(result).to(eq(33))


# ============================================================================
# Backward Pipeline
# ============================================================================

describe "Pipeline Operators - Backward":
    """
    ## Backward Pipeline

    The backward pipeline `<|` applies functions right-to-left.
    Useful for reducing parentheses in function applications.
    """

    context "with function application":
        """
        ### Scenario: Avoiding Parentheses

        Using backward pipeline to apply functions without nesting parentheses.

        ```simple
        val result = triple <| add_one <| double <| 5
        # Equivalent to: triple(add_one(double(5)))
        ```
        """

        it "applies functions right-to-left":
            fn double(x: Int) -> Int:
                x * 2

            fn add_one(x: Int) -> Int:
                x + 1

            fn triple(x: Int) -> Int:
                x * 3

            val result = triple <| add_one <| double <| 5
            expect(result).to(eq(33))


# ============================================================================
# Type Inference
# ============================================================================

describe "Pipeline Operators - Type Inference":
    """
    ## Type Inference Through Pipelines

    The type checker infers types through pipeline chains.
    """

    context "with generic functions":
        """
        ### Scenario: Automatic Type Inference

        Generic functions are instantiated based on pipeline context.

        ```simple
        val result = [1, 2, 3]
            |> map(double)      # List[Int] -> List[Int]
            |> filter(is_even)  # List[Int] -> List[Int]
            |> sum              # List[Int] -> Int
        ```
        """

        it "infers types correctly":
            fn is_even(x: Int) -> Bool:
                x % 2 == 0

            val result = [1, 2, 3, 4, 5, 6]
                |> filter(is_even)
                |> sum

            expect(result).to(eq(12))  # 2 + 4 + 6


# ============================================================================
# Partial Application
# ============================================================================

describe "Pipeline Operators - Partial Application":
    """
    ## Partial Application with Pipelines

    Pipelines support partial application for multi-argument functions.
    """

    context "with multi-argument functions":
        """
        ### Scenario: Currying and Pipelines

        When piping into a partially applied function, the piped value
        becomes the last argument.

        ```simple
        val result = 10
            |> add(5)      # add(5, 10) = 15
            |> multiply(2) # multiply(2, 15) = 30
        ```
        """

        it "passes value as last argument":
            fn add(a: Int, b: Int) -> Int:
                a + b

            fn multiply(a: Int, b: Int) -> Int:
                a * b

            val result = 10
                |> add(5)      # add(5, 10) = 15
                |> multiply(2) # multiply(2, 15) = 30

            expect(result).to(eq(30))


# ============================================================================
# Edge Cases
# ============================================================================

describe "Pipeline Operators - Edge Cases":
    """
    ## Edge Case Handling

    Tests for unusual or complex pipeline scenarios.
    """

    context "with operator precedence":
        """
        ### Scenario: Pipeline vs Arithmetic Precedence

        Pipelines have lower precedence than arithmetic operators.

        ```simple
        val result = 5 + 3 |> double  # (5 + 3) |> double = 16
        ```
        """

        it "evaluates arithmetic before pipeline":
            fn double(x: Int) -> Int:
                x * 2

            val result = 5 + 3 |> double
            expect(result).to(eq(16))

    context "with method calls":
        """
        ### Scenario: Method Chaining with Pipelines

        Pipelines work with method calls.

        ```simple
        val result = "hello"
            |> uppercase()
            |> append("!")
        ```
        """

        it "chains method calls":
            val result = "hello"
                |> uppercase()
                |> append(" world")

            expect(result).to(eq("HELLO world"))


# ============================================================================
# Helper Functions
# ============================================================================

fn double(x: Int) -> Int:
    x * 2

fn add_one(x: Int) -> Int:
    x + 1

fn triple(x: Int) -> Int:
    x * 3

fn is_even(x: Int) -> Bool:
    x % 2 == 0

fn add(a: Int, b: Int) -> Int:
    a + b

fn multiply(a: Int, b: Int) -> Int:
    a * b

fn filter<T>(pred: fn(T) -> Bool, list: List<T>) -> List<T>:
    # Filter implementation
    pass

fn sum(list: List<Int>) -> Int:
    # Sum implementation
    pass
```

## Step 3: Run Tests

```bash
# Build first
cargo build

# Run the spec
cargo test -p simple-driver simple_stdlib_system_pipeline_operators

# Or run directly
./target/debug/simple simple/test/system/features/pipeline_operators/pipeline_operators_spec.spl
```

Expected output:
```
Pipeline Operators - Basic
  ✓ applies function to value
  ✓ chains multiple operations

Pipeline Operators - Backward
  ✓ applies functions right-to-left

Pipeline Operators - Type Inference
  ✓ infers types correctly

Pipeline Operators - Partial Application
  ✓ passes value as last argument

Pipeline Operators - Edge Cases
  ✓ evaluates arithmetic before pipeline
  ✓ chains method calls

7 tests, 0 failures
```

## Step 4: Generate Documentation

```bash
# Generate docs using the full generator
cargo run --bin gen-sspec-docs -- \
  simple/test/system/features/pipeline_operators/pipeline_operators_spec.spl

# Output will be in doc/spec/pipeline_operators_spec.md
```

## Step 5: Review Generated Documentation

The generator creates `doc/spec/pipeline_operators_spec.md`:

```markdown
# Pipeline Operators Specification

*Source: `simple/test/system/features/pipeline_operators/pipeline_operators_spec.spl`*
*Last Updated: 2026-01-16*

## Feature IDs

- <a id="feature-450"></a>#450
- <a id="feature-451"></a>#451
- <a id="feature-452"></a>#452
- <a id="feature-453"></a>#453
- <a id="feature-454"></a>#454
- <a id="feature-455"></a>#455

---

**Feature IDs:** #450-455
**Category:** Language
**Difficulty:** 3/5
**Status:** Implemented

## Overview

Pipeline operators enable functional composition by passing the result of one
expression as input to the next...

[Full module documentation extracted]

## Basic Forward Pipeline

The forward pipeline `|>` passes a value to the next function.

### Scenario: Single Function Application

Applying one function to a value using the pipeline operator.

```simple
val result = 5 |> double
# Equivalent to: double(5)
```

[And so on...]
```

## Step 6: View in Index

The index (`doc/spec/README.md`) automatically includes your spec:

```markdown
## Language

- [Pipeline Operators Specification](pipeline_operators_spec.md) - #450-455 - Implemented
- [Other Language Features...](...)
```

## Key Takeaways

1. **Start with the template** - `.claude/templates/sspec_template.spl`
2. **Required metadata** - Feature IDs, Category, Status in module docstring
3. **Document as you write** - Add `"""..."""` docstrings to describe/context blocks
4. **Test first** - Ensure tests pass before generating docs
5. **Use the full generator** - `gen-sspec-docs` for complete feature specs
6. **Review output** - Generated docs should be readable and complete

## Common Patterns

### Pattern: Feature with Multiple Aspects

Organize into logical test groups:

```simple
describe "Feature - Basic":
    # Basic functionality tests

describe "Feature - Advanced":
    # Complex scenarios

describe "Feature - Edge Cases":
    # Edge cases and error handling
```

### Pattern: Cross-Referenced Features

Link to related specs in module docstring:

```simple
"""
## Related Specifications

- [Functions](functions.md) - Function syntax
- [Type Inference](type_inference.md) - Type checking
"""
```

### Pattern: Examples in Documentation

Include executable examples in docstrings:

```simple
"""
### Example: Basic Usage

```simple
val result = use_feature()
```

This demonstrates...
"""
```

## Troubleshooting

### Issue: Tests pass but no documentation generated

**Solution:** Ensure you have `"""..."""` docstrings in your spec file. The generator only extracts triple-quoted strings.

### Issue: Metadata not showing up in index

**Solution:** Check that your module-level docstring has the required format:
- Must be at the very top of the file (before imports)
- Must include `**Feature IDs:**` and `**Category:**`

### Issue: Generated docs are incomplete

**Solution:** Run with validation to see warnings:
```bash
cargo run --bin gen-sspec-docs -- your_spec.spl
```

The generator will show warnings for:
- Missing sections
- Short documentation (< 10 lines)
- Missing metadata fields
