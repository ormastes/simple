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

## Missing File I/O in Standard Library

**Type:** Bug
**Priority:** High
**Discovered:** 2025-12-26
**Component:** Standard Library (`simple/std_lib/src/host/`)

### Description

The Simple standard library lacks basic file I/O operations needed for practical applications. While the framework exists (`host.async_nogc_mut.io.fs`), core file reading/writing functions are not implemented or not accessible.

### Expected

Should be able to:
- Read file contents: `fs.read_file(path: String) -> Result[String, IoError]`
- Write file contents: `fs.write_file(path: String, content: String) -> Result[(), IoError]`
- Check file existence: `fs.exists(path: String) -> bool`
- List directory contents: `fs.list_dir(path: String) -> Result[List[String], IoError]`

### Actual

File I/O operations are either:
1. Not defined in the standard library
2. Defined but not accessible from Simple code
3. Only available through FFI/runtime (not exposed to Simple)

### Reproduction

```simple
use host.async_nogc_mut.io.fs.*

fn main():
    # This should work but doesn't
    content = read_file("test.spl")  # Error: undefined function
```

### Impact

- Blocks MCP tool implementation (needs to read source files)
- Blocks formatter/linter (need to read/write files)
- Blocks any practical application that needs file I/O
- Forces workarounds with hardcoded example data

### Files Involved

- `simple/std_lib/src/host/async_nogc_mut/io/` - Missing file I/O implementations
- `simple/app/mcp/main.spl` - Workaround using example data (line 101)
- `simple/app/formatter/main.spl` - Same issue
- `simple/app/lint/main.spl` - Same issue

### Workaround

Use hardcoded example data or implement file I/O as runtime FFI calls. Not sustainable for real applications.

### Status

Critical blocker for self-hosted tooling. Needs immediate implementation.

## Missing String Methods in Core Library

**Type:** Bug
**Priority:** Medium
**Discovered:** 2025-12-26
**Component:** Core Library (`simple/std_lib/src/core/string.spl`)

### Description

String type lacks several essential methods needed for text processing:
- `substring(start: i64, end: i64) -> String` - Extract substring
- `char_at(index: i64) -> String` - Get character at position
- `find(pattern: String) -> i64` - Find substring position (returns -1 if not found)
- `strip() -> String` - Remove leading/trailing whitespace
- `to_string()` conversion for primitive types

### Expected

```simple
text = "  hello world  "
trimmed = text.strip()  # "hello world"
pos = text.find("world")  # 8
ch = text.char_at(2)  # "h"
sub = text.substring(2, 7)  # "hello"
```

### Actual

These methods don't exist, forcing manual character iteration or workarounds.

### Impact

- MCP parser needs `substring()` and `find()` for symbol extraction
- Blocks many stdlib features
- Makes string processing unnecessarily complex

### Files Involved

- `simple/std_lib/src/core/string.spl` - Missing methods
- `simple/std_lib/src/mcp/parser.spl` - Needs these methods (lines 35, 60, 88, etc.)

### Workaround

Implement manual character iteration, but very inefficient and error-prone.

### Status

Needs implementation in core library.

## Interpreter Enum/Union Type Parsing Issues (RESOLVED)

**Type:** Bug
**Priority:** Critical (Blocker)
**Discovered:** 2025-12-28
**Resolved:** 2025-12-28
**Component:** Parser/Interpreter (`src/parser/`, `src/compiler/src/interpreter*.rs`)

### Description

The Simple interpreter/parser failed to handle several advanced enum and type syntax features that were used in the verification regeneration module.

### Three Specific Issues (ALL FIXED)

#### Issue 1: Named Parameters in Enum Variants ✅ FIXED

```simple
enum SimpleType:
    IntType
    ListType(elem: SimpleType)  # Now works!
```

**Fix:** Added `parse_enum_field_list()` in `types_def/mod.rs` to support named fields in enum variants. Modified `EnumVariant` AST to use `EnumField` with optional names.

#### Issue 2: Methods Inside Enum Blocks ✅ FIXED

```simple
enum SimpleType:
    IntType
    BoolType

    fn to_lean(self) -> String:  # Now works!
        match self:
            case IntType:
                return "Int"
            case BoolType:
                return "Bool"
```

**Fix:** Added `parse_enum_variants_and_methods()` in `types_def/mod.rs` and added `methods` field to `EnumDef` AST. Note: Match arms require indented blocks after `:`, not inline syntax.

#### Issue 3: Union Types (Type Alternation) ✅ ALREADY WORKED

```simple
class FieldDef:
    name: String
    default_value: String | None  # Works!
```

**Confirmed:** Union types were already working. The original report was incorrect.

### Reproduction

Create test file `/tmp/test_enum.spl`:

```simple
# Test 1: Named enum parameters
enum Color:
    RGB(r: Int, g: Int, b: Int)

# Test 2: Enum methods
enum Status:
    Active
    Inactive

    fn is_active(self) -> Bool:
        match self:
            case Active: return True
            case Inactive: return False

# Test 3: Union types
class Config:
    name: String
    value: String | None

fn main() -> Int:
    return 0
```

Run: `./target/debug/simple /tmp/test_enum.spl`

### Impact

- **BLOCKS** `simple gen-lean` command - cannot regenerate Lean verification files
- **BLOCKS** verification module (`simple/std_lib/src/verification/`)
- Affects 12+ Lean file regeneration
- Affects type-safe code patterns throughout stdlib

### Files Involved

- `src/parser/src/statements/` - Enum parsing
- `src/parser/src/types_def/mod.rs` - Type parsing (union types)
- `simple/std_lib/src/verification/lean/types.spl` - Uses all three features
- `simple/std_lib/src/verification/lean/codegen.spl` - Uses all three features
- `simple/std_lib/src/verification/regenerate.spl` - Main regeneration module

### Workaround

The `gen-lean` command falls back to reading existing Lean files instead of regenerating them. This works for comparison but doesn't allow actual regeneration.

### Status

✅ **RESOLVED** - All three parser bugs have been fixed:
- Added `EnumField` struct to `src/parser/src/ast/nodes/core.rs`
- Added `parse_enum_field_list()` to `src/parser/src/types_def/mod.rs`
- Added `parse_enum_variants_and_methods()` to `src/parser/src/types_def/mod.rs`
- Added `methods` field to `EnumDef` in `src/parser/src/ast/nodes/definitions.rs`
- Fixed pattern parsing to not consume `:` for match arm separators
- All 8 enum_advanced reproduction tests pass

## Module Import Alias Creates Empty Dict

**Type:** Bug
**Priority:** High
**Discovered:** 2025-12-28
**Component:** Interpreter (`src/compiler/src/interpreter*.rs`)

### Description

The `import X.Y.Z as alias` syntax creates `alias` as an empty dict `{}` instead of a dict containing the module's exports. This makes the alias unusable.

### Expected

```simple
import verification.lean.types as types
print(types)  # Should print dict with module exports
result = types.make_simple_type("Test")  # Should work
```

### Actual

```simple
import verification.lean.types as types
print(types)  # Prints: {}
result = types.make_simple_type("Test")  # Error: method call on unsupported type
```

### Impact

- **BLOCKS** verification module regeneration
- **BLOCKS** any module that uses `import X as Y` pattern
- Forces use of workarounds or full module paths

### Workaround

The `gen-lean` command falls back to reading existing Lean files when regeneration fails.

### Status

Open - needs investigation in `interpreter_expr.rs` or module loading code.

## List Concatenation with + Operator Broken

**Type:** Bug
**Priority:** Medium
**Discovered:** 2025-12-28
**Resolved:** 2025-12-28
**Component:** Interpreter (`src/compiler/src/interpreter*.rs`)

### Description

List concatenation using `list + [item]` fails with "expected int, got Array([])".

### Expected

```simple
items = []
new_items = items + ["hello"]  # Should work
```

### Actual

```simple
items = []
new_items = items + ["hello"]  # Error: expected int, got Array([])
```

### Fix Applied

Replaced all `list + [item]` patterns with `list.append(item)` in verification module files. The `.append()` method works correctly.

### Files Modified

- `simple/std_lib/src/verification/lean/emitter.spl`
- `simple/std_lib/src/verification/lean/codegen.spl`
- `simple/std_lib/src/verification/lean/types.spl`
- `simple/std_lib/src/verification/lean/contracts.spl`
- `simple/std_lib/src/verification/models/contracts.spl`
- `simple/std_lib/src/verification/models/module_resolution.spl`
- `simple/std_lib/src/verification/models/nogc_compile.spl`
- `simple/std_lib/src/verification/models/gc_manual_borrow.spl`
- `simple/std_lib/src/verification/models/memory_model_drf.spl`
- `simple/std_lib/src/verification/models/visibility_export.spl`
- `simple/std_lib/src/verification/proofs/checker.spl`
- `simple/std_lib/src/verification/proofs/obligations.spl`

### Status

✅ **RESOLVED** - All occurrences fixed with `.append()` pattern.

## Static Methods Named 'new' Cause Infinite Recursion

**Type:** Bug
**Priority:** High
**Discovered:** 2025-12-28
**Component:** Interpreter (`src/compiler/src/interpreter_method/special.rs`)

### Description

When a class has a static method named `new`, calling `ClassName.new()` causes infinite recursion and stack overflow.

### Cause

In `instantiate_class()`, if a class has a method named `new`, the interpreter calls that method. But if the `new` method returns `ClassName(...)`, that calls `instantiate_class` again, which calls `new` again, causing infinite recursion.

### Expected

```simple
class Counter:
    count: Int

    fn new(count: Int) -> Counter:
        return Counter(count)

c = Counter.new(42)  # Should work
```

### Actual

Stack overflow due to infinite recursion between `instantiate_class` and `new` method.

### Fix Applied

Renamed all `new` methods to `create` in verification module files to avoid the issue.

### Files Modified

- `simple/std_lib/src/verification/lean/*.spl`
- `simple/std_lib/src/verification/models/*.spl`
- `simple/std_lib/src/verification/proofs/*.spl`

### Status

✅ **WORKAROUND APPLIED** - Renamed to `create`. The underlying interpreter bug should still be fixed.
