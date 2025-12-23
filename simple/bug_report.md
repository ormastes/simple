# Bug Reports

## BDD Spec Framework Scoping Issue  

**Type:** Bug
**Priority:** High  
**Discovered:** 2025-12-23
**Component:** BDD Spec Framework (`simple/std_lib/src/spec/`)

### Description

The BDD spec framework has a scoping issue where functions defined inside `it` blocks cause semantic analysis errors after the test completes. Tests pass successfully but then fail with "semantic: undefined variable" errors.

### Expected

Functions defined inside `it` blocks should be scoped only to that block and should not cause errors after the block completes.

### Actual  

Tests execute and pass ("N examples, 0 failures" is printed), but then a semantic error occurs referencing variables that were only defined inside the `it` block.

### Reproduction

```simple
use spec.*

describe "test":
    it "defines function":
        fn square(x: i64) -> i64:
            return x * x

        result = square(5)
        expect(result).to_equal(25)
```

Output:
```
test
  ✓ defines function

1 example, 0 failures
error: compile failed: semantic: undefined variable: square
```

### Workaround

Define functions at module level instead of inside `it` blocks. However, this causes different errors with method calls.

### Impact

- Blocks testing of decorators (#1069-#1072) which require function definitions in tests
- Blocks testing of any feature that requires scoped function definitions  
- Affects 15+ stdlib tests

### Files Involved

- `simple/std_lib/src/spec/dsl.spl` - `describe` and `it` block implementation
- `simple/std_lib/test/unit/core/decorators_spec.spl` - Affected test
- `src/compiler/src/interpreter_expr.rs:326` - Where semantic error is generated

### Root Cause (Hypothesis)

The spec framework appears to be evaluating or analyzing code after `it` block closures complete, trying to access variables that were only in scope during the closure execution.

### Status

Investigating. Decorators are fully implemented (#1069-#1072) but cannot be tested until this is resolved.

## BDD Spec Framework Mutable Variable Issue

**Type:** Bug
**Priority:** Medium
**Discovered:** 2025-12-23
**Component:** BDD Spec Framework (`simple/std_lib/src/spec/`)

### Description

The BDD spec framework doesn't properly support mutable variables inside `it` blocks. The functional update operator `->` and other mutations don't work on `let mut` variables defined within `it` closures.

### Expected

Mutable variables defined with `let mut` inside `it` blocks should be properly mutable and support the functional update operator `->`.

### Actual

Mutable variables behave as immutable. The functional update operator `->` doesn't modify the variable.

### Reproduction

```simple
use spec.*

describe "Test":
    it "uses mutable variable":
        let mut arr = [1, 2]
        arr->concat([3, 4])
        expect arr.len() == 4  # Fails: arr.len() is still 2
```

Output:
```
Test
  ✗ uses mutable variable
    expected 2 to equal 4

1 example, 1 failure
```

### Workaround

Test mutable operations outside the BDD framework. The feature works correctly in normal code - only BDD framework closures are affected.

### Impact

- Blocks BDD testing of fluent interface features (#1068)
- May affect other features requiring mutable variables in tests
- Feature itself is working correctly (proven by Rust tests and direct execution)

### Files Involved

- `simple/std_lib/src/spec/dsl.spl` - `it` block closure implementation
- `simple/std_lib/test/unit/core/fluent_interface_spec.spl` - Affected test

### Root Cause (Hypothesis)

The closure environment created by `it` blocks may be capturing variables by value instead of by reference, or not properly handling mutable captures.

### Status

Documented. Fluent interface (#1068) is complete and working - this BDD bug doesn't block the feature itself.

## Formatter/Linter Compilation Blockers

**Type:** Bug
**Priority:** Medium
**Discovered:** 2025-12-23
**Component:** Formatter (`simple/app/formatter/main.spl`), Linter (`simple/app/lint/main.spl`)

### Description

Formatter and linter source code is complete but won't compile due to parsing errors. Error: "Unterminated f-string" even after removing all f-string usage.

### Work Completed

- ✅ Fixed generic type syntax from `Result<T, E>` to `Result[T, E]` (Simple uses square brackets)
- ✅ Fixed multi-line boolean expressions (added explicit `return`)
- ✅ Replaced f-strings with string concatenation to avoid interpolation issues
- ✅ Source code is functionally complete (166 lines formatter, 262 lines linter)

### Remaining Issues

1. Parser reports "Unterminated f-string" error despite no f-strings in code
2. May be related to how the parser processes imports or class definitions
3. Needs deeper investigation into lexer/parser state

### Status

Blocked on parser bug. Source code is complete and ready for compilation once parser issue is resolved.

### Workaround

None currently. Formatter and linter functionality is implemented but cannot be compiled/tested.
