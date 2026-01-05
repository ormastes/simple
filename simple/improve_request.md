# Improvement Requests

Track improvement ideas discovered while developing Simple standard library and applications.

## Summary (Updated 2026-01-05)

| Improvement | Status | Priority |
|-------------|--------|----------|
| Multi-Line Method Chaining | ⏸️ Deferred (infra added) | Medium |
| Triple-Quoted F-Strings | 📋 Proposed | Low |
| String Multiplication | ✅ Implemented | Low |
| Match Arrow Syntax | ✅ Implemented | High |
| Function Return Type Annotations | ✅ Implemented | High |
| Generic Type Syntax | ✅ Implemented | High |
| Enum Variant Construction | ✅ Implemented | Medium |
| Qualified Method Chains | ✅ Implemented | Medium |
| Struct Literal Construction | ✅ Implemented | Medium |
| Reserved Keyword Handling | ✅ Implemented | High |
| Multi-line Dict Literals | ✅ Implemented | Medium |
| Comprehensive File I/O API | ✅ Partial (native funcs) | High |
| Enhanced String Methods | ✅ Implemented | High |
| JSON Library | ⚠️ Blocked (import bug) | Medium |
| Error Handling (`?` operator) | ✅ Implemented | Medium |
| Symbol Table Cross-Refs | 📋 Proposed | Low |

**Summary:** 11 implemented, 1 partial, 1 blocked (JSON - import bug), 1 deferred, 2 proposed

**What Remains:**
- **JSON Library** - Implementation complete, but `import core.json` hangs (see bug_report.md)
- **Triple-Quoted F-Strings** - Proposed, low priority
- **Symbol Table Cross-Refs** - Proposed, low priority
- **Multi-Line Method Chaining** - Deferred (infrastructure added)

---

## Template

```markdown
### [Component] Brief description

**Type:** Improvement
**Category:** API Design | Performance | DX | Feature | Stdlib
**Priority:** High | Medium | Low
**Proposed:** YYYY-MM-DD
**Status:** Proposed | Accepted | Implemented | Rejected

**Problem:**
[What problem does this solve?]

**Proposed Solution:**
[How should we solve it?]

**Example:**
```simple
[Code example showing the improvement]
```

**Benefits:**
- [Benefit 1]
- [Benefit 2]

**Alternatives Considered:**
[Other approaches and why this is preferred]

**Impact:**
- Breaking changes: Yes/No
- Migration path: [if applicable]
```

---

## Active Requests

<!-- Add new improvement requests below this line -->

### [Parser] Multi-Line Method Chaining Support

**Type:** Improvement
**Category:** DX
**Priority:** Medium
**Proposed:** 2026-01-01
**Status:** Deferred (Infrastructure Added 2026-01-04)

**Problem:**
Method chaining across multiple lines fails to parse, forcing developers to use single-line chains or intermediate variables:

**Current Behavior:**
```simple
# Doesn't work - parse error: "expected expression, found Indent"
let parser = cli.ArgParser::new("test", "Test")
    .flag("verbose", "v", "Enable verbose output")
    .required_option("output", "o", "Output file")
```

**Proposed Solution:**
Extend the postfix expression parser to recognize the pattern `NEWLINE → INDENT → DOT` as method chain continuation.

**Example:**
```simple
# Should work: Multi-line builder pattern
let parser = cli.ArgParser::new("test", "Test")
    .flag("verbose", "v", "Enable verbose output")
    .required_option("output", "o", "Output file")
    .required_positional("input", "Input file")

# Should work: Chained transformations
let result = data
    .filter(\x: x > 0)
    .map(\x: x * 2)
    .sum()

# Current workaround 1: Single line (hard to read)
let parser = cli.ArgParser::new("test", "Test").flag("verbose", "v", "Enable verbose output").required_option("output", "o", "Output file")

# Current workaround 2: Intermediate variables (verbose)
let parser = cli.ArgParser::new("test", "Test")
let parser = parser.flag("verbose", "v", "Enable verbose output")
let parser = parser.required_option("output", "o", "Output file")
```

**Benefits:**
- Improved code readability for builder patterns
- More natural API design (fluent interfaces)
- Consistent with Rust, JavaScript, and other modern languages
- Reduces need for horizontal scrolling
- Better fits indentation-based syntax

**Alternatives Considered:**
1. **Require explicit continuation marker** (like `\` in Python)
   - Pros: Explicit, no ambiguity
   - Cons: Adds visual noise, breaks fluent interface feel

2. **Use parentheses to group** (like some languages)
   ```simple
   let parser = (cli.ArgParser::new("test", "Test")
       .flag("verbose", "v", "Enable verbose output"))
   ```
   - Pros: Clear grouping
   - Cons: Breaks indentation-based syntax feel

3. **Accept the limitation** (current state)
   - Pros: No parser changes needed
   - Cons: Poor developer experience, inconsistent with expectations

**Technical Challenges:**
- NEWLINE tokens serve dual purpose: expression terminators AND whitespace
- ~~Current `pending_token` mechanism can only store one token~~ **FIXED:** Changed to `VecDeque<Token>` buffer
- Naively consuming NEWLINE in postfix loop breaks if-statement, match, and other statement parsing
- INDENT/DEDENT balancing is complex - need to track depth properly

**Infrastructure Added (2026-01-04):**
1. ✅ Changed `pending_token: Option<Token>` to `pending_tokens: VecDeque<Token>` for multi-token lookahead
2. ✅ Updated `advance()` and all peek functions to use the new buffer
3. ✅ Added `peek_through_newlines_and_indents_is()` helper function
4. ⏸️ Deferred: Actual multi-line chaining implementation needs proper INDENT/DEDENT depth tracking

**Remaining Work:**
1. Track INDENT/DEDENT depth to properly handle nested blocks
2. In postfix expression loop, when encountering NEWLINE:
   - Peek ahead through NEWLINE and any INDENT tokens
   - If next non-whitespace token is DOT, consume the whitespace and continue
   - Otherwise, break from postfix loop (NEWLINE terminates expression)
3. Ensure this doesn't break statement parsing (if, match, let, etc.)
4. Add comprehensive parser tests for regressions

**Files Changed:**
- `src/parser/src/parser_impl/core.rs` - `pending_tokens: VecDeque<Token>`
- `src/parser/src/parser_helpers.rs` - Updated peek functions with buffer support

**Impact:**
- Breaking changes: No (only adds new capability)
- Files affected: ~20 stdlib test files currently work around this limitation
- Parser files: `src/parser/src/expressions/mod.rs` (postfix loop), token buffer implementation
- Migration path: Existing code continues to work, new code can use multi-line chaining

**Related:**
- Currently affects 20 stdlib test failures
- Documented in `doc/report/PARSER_FIXES_2026-01-01.md`
- Parser postfix loop: `src/parser/src/expressions/mod.rs:617-875`

---

### [Parser] Triple-Quoted F-String Support

**Type:** Improvement
**Category:** Feature
**Priority:** Low
**Proposed:** 2025-12-29
**Status:** Proposed

**Problem:**
F-strings with triple quotes (`f"""..."""`) cause "Unterminated f-string" parse errors.

**Current Spec Behavior:**
- `"..."` or `f"..."` - Interpolated strings (supports `{expr}`)
- `'...'` - Raw strings (NO interpolation, NO escapes)
- `"""..."""` - Doc comments only (not string values)

Triple-quoted strings are currently only for documentation comments, not multi-line string values with interpolation.

**Proposed Solution:**
Add parser support for `f"""..."""` (triple-quoted f-strings) to allow multi-line string templates with interpolation, without requiring `\n` escapes.

**Example:**
```simple
# Works: Single-line f-string
let msg = f"Hello, {name}!"

# Works: F-string with \n escapes
let markdown = f"# {name}\n\n**ID:** #{id}\n"

# Doesn't work: Triple-quoted f-string
let markdown = f"""# {name}

**ID:** #{id}
"""
# Error: Unterminated f-string

# Current workaround: Use \n escapes
let markdown = f"# {name}\n\n**ID:** #{id}\n"
```

**Benefits:**
- More readable multi-line templates
- Consistent with Python f-strings
- Natural formatting for markdown/HTML generation
- Reduces need for `\n` escapes

**Alternatives Considered:**
- Use `\n` escapes - current workaround, works but less readable
- Use string concatenation - more verbose
- Regular triple-quoted strings - no interpolation

**Impact:**
- Breaking changes: No (new feature addition)
- Files affected: Templates and documentation generators
- Related: BDD Feature Documentation (#SESSION-6)

**Note:** Single-line f-strings work perfectly. This is only about triple-quoted multi-line f-strings.

---

### [Core] String Multiplication Operator

**Type:** Improvement
**Category:** Feature
**Priority:** Low
**Proposed:** 2025-12-29
**Status:** ✅ Implemented (verified 2026-01-04)

**Problem:**
String multiplication syntax (`"x" * n`) is not supported, forcing manual repetition for common patterns like separators and padding.

**Proposed Solution:**
Implement string multiplication operator to repeat strings:

**Example:**
```simple
# Desired syntax (doesn't work):
separator = "=" * 60
indent = " " * 4

# Current workaround (manual):
separator = "============================================================"
indent = "    "
```

**Benefits:**
- Cleaner code for repeated strings
- Common pattern in Python and other languages
- Useful for formatting and alignment
- Reduces magic constants

**Alternatives Considered:**
- Repeat function: `String.repeat("x", n)` - more verbose but could work
- Manual repetition - current approach, error-prone

**Impact:**
- Breaking changes: No (new feature)
- Migration path: Optional, manual strings still work
- Implementation: Operator overloading in interpreter/codegen

---

### [Parser] Match Expression Arrow Syntax Support

**Type:** Improvement
**Category:** Feature
**Priority:** High
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (verified 2026-01-04)

**Problem:**
Match expressions with arrow syntax (`->`) are specified in the language but not implemented in the parser. This blocks compilation of idiomatic Simple code including the LMS implementation.

**Proposed Solution:**
Implement parser support for match expressions with arrow syntax:

**Example:**
```simple
match value:
    Some(x) ->
        x + 1
    None ->
        0
```

Current parser expects `case Pattern:` but language spec requires `Pattern ->`.

**Benefits:**
- Enables functional pattern matching style
- Matches language specification
- Unblocks LMS server implementation (~930 lines)
- Consistent with Rust/ML-family language syntax

**Alternatives Considered:**
- Keep `case Pattern:` syntax - rejected (not in spec)
- Support both syntaxes - adds complexity

**Impact:**
- Breaking changes: No (feature addition)
- Files blocked: error.spl, protocol.spl, server.spl
- Related: #1200-1209 (LMS implementation)

---

### [Parser] Function Return Type Annotations

**Type:** Improvement
**Category:** Feature
**Priority:** High
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (verified 2026-01-04)

**Problem:**
Function return type annotations (`fn name() -> Type:`) are not parsed correctly. Parser fails with "expected identifier, found Result/Option/etc".

**Proposed Solution:**
Implement parser support for `-> Type` return type syntax in function signatures.

**Example:**
```simple
fn read_file(path: String) -> Result[String, Error]:
    # implementation
```

**Benefits:**
- Type safety and documentation
- Required for Result/Option return types
- Enables compiler type checking
- Matches language specification

**Alternatives Considered:**
- Type inference only - loses explicit documentation and early error detection

**Impact:**
- Breaking changes: No (feature addition)
- Files blocked: All LMS files (transport.spl, error.spl, protocol.spl, session.spl, server.spl, main.spl)
- Related: #1200-1209 (LMS implementation)

---

### [Parser] Generic Type Syntax in Type Positions

**Type:** Improvement
**Category:** Feature
**Priority:** High
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (verified 2026-01-04)

**Problem:**
Generic types like `Result[T, E]`, `Option[T]`, `Dict[K, V]` are not recognized by the parser in return type positions and field declarations.

**Proposed Solution:**
Implement parser support for square bracket generic syntax in all type positions.

**Example:**
```simple
class Server:
    cache: Dict[String, String]
    session: Option[Session]

fn process() -> Result[Int, Error]:
    Ok(42)
```

**Benefits:**
- Enables type-safe collections and error handling
- Required for Result/Option types
- Matches modern language conventions
- Unblocks stdlib development

**Alternatives Considered:**
- Use angle brackets `<>` - conflicts with comparison operators
- No generics - loses type safety

**Impact:**
- Breaking changes: No (feature addition)
- Files blocked: All LMS files
- Related: #1200-1209 (LMS implementation)

---

### [Parser] Enum Variant Construction Syntax ✅ IMPLEMENTED

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** ✅ IMPLEMENTED (2026-01-04)

**Implementation:**
Enum variant construction with `EnumName.Variant(args)` syntax is now fully supported.

The implementation includes:
1. `Value::EnumType` - Represents an enum type (like `Color`)
2. `Value::EnumVariantConstructor` - Represents a variant constructor for variants with data
3. Enum types are registered in the environment during module evaluation
4. Identifier resolution checks enums and returns `EnumType`
5. Field access on `EnumType` returns the variant value (unit) or constructor
6. Method calls on `EnumType` construct variants with data

**Example:**
```simple
enum LmsError:
    MethodNotFound(String)
    InvalidParams(String)

let error = LmsError.MethodNotFound("initialize")  # Works!

enum Color:
    Red
    Green
    Blue

let c = Color.Red  # Works!
```

**Files Changed:**
- `src/compiler/src/value.rs` - Added `EnumType`, `EnumVariantConstructor` variants
- `src/compiler/src/interpreter_eval.rs` - Register enums in env
- `src/compiler/src/interpreter_expr.rs` - Enum lookup in identifier resolution, field access handling
- `src/compiler/src/interpreter_method/mod.rs` - Method call handling for variant construction
- `src/compiler/src/interpreter_module.rs` - Export enums as `EnumType`
- `src/compiler/src/interpreter_call/mod.rs` - Call handling for `EnumVariantConstructor`
- `src/compiler/src/value_*.rs` - Pattern matching updates

---

### [Parser] Qualified Method Call Chains ✅ IMPLEMENTED

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (2026-01-05)

**Implementation:**
Multi-level qualified method calls and field access work correctly. The previous issue was testing with non-existent modules.

**Example:**
```simple
class Time:
    fn now_ms() -> Int:
        return 1000

class Sys:
    time: Time

let sys = Sys { time: Time {} }
let timestamp = sys.time.now_ms()  # Works: 1000
let name = session.client_info.name  # Works if objects exist
```

**What Works:**
- `outer.middle.inner.method()` - Chained field access + method call
- `a.b.c.d()` - Any depth of nesting
- Method calls with arguments on nested objects

**Benefits:**
- Enables namespace organization
- Required for stdlib module structure
- Natural method chaining

**Note:** The original report of "expected Comma, found Dot" was likely due to testing with undefined modules.

---

### [Parser] Struct Literal Construction Syntax

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (verified 2026-01-04)

**Problem:**
Struct/class construction with field names `ClassName { field: value }` is not parsed.

**Proposed Solution:**
Support struct literal syntax for class instantiation.

**Example:**
```simple
let info = protocol.ClientInfo {
    name: "claude",
    version: "1.0.0"
}
```

**Benefits:**
- Clear field initialization
- Self-documenting code
- Prevents field order mistakes

**Alternatives Considered:**
- Positional construction only - error-prone for many fields

**Impact:**
- Breaking changes: No (feature addition)
- Files blocked: server.spl, protocol.spl
- Related: #1200-1209 (LMS implementation)

---

### [Parser] Reserved Keyword Handling for Parameter Names

**Type:** Improvement
**Category:** Feature
**Priority:** High
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (2025-12-25)

**Problem:**
Using `result` as a parameter name causes "expected identifier, found Result" error because `Result` is a built-in type. The parser treats lowercase `result` as conflicting with the capitalized `Result` type.

**Proposed Solution:**
Allow lowercase identifiers that match type names (e.g., `result`, `option`, `string`) to be used as parameter/variable names. Only treat capitalized identifiers as type references in type positions.

**Example:**
```simple
# Should work:
pub fn success_response(id: Int, result: Dict) -> Dict:
    return {"jsonrpc": "2.0", "id": id, "result": result}

# Currently fails with "expected identifier, found Result"
```

**Benefits:**
- Natural parameter naming (e.g., `result` for Result types)
- Matches conventions in other languages (Rust allows `result` variable names)
- Less surprising behavior

**Alternatives Considered:**
- Rename all conflicting parameters (current workaround) - verbose and unnatural
- Make `Result` not a keyword - would break type system

**Impact:**
- Breaking changes: No (relaxing restrictions)
- Files affected: error.spl, transport.spl, protocol.spl (can now use original parameter names)
- Related: #1200-1209 (LMS implementation)

**Implementation:**
Modified `expect_identifier()` in `src/parser/src/parser_helpers.rs` to accept contextual keywords (`Result`, `Type`, `Out`, `OutErr`) as identifiers. These tokens are now treated as regular identifiers in parameter/variable contexts while remaining keywords only in their specific contract/type contexts.

---

### [Parser] Multi-line Dictionary Literal Support

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** ✅ Implemented (2025-12-25)

**Problem:**
Dict literals cannot span multiple lines. Opening brace on new line or nested structures fail with "expected expression, found Newline".

**Proposed Solution:**
Support multi-line Dict literals with proper indentation handling, similar to Python dicts or JSON.

**Example:**
```simple
# Should work:
let response = {
    "jsonrpc": "2.0",
    "id": id,
    "error": {
        "code": code,
        "message": message
    }
}

# Currently must be single-line:
let error_obj = {"code": code, "message": message}
let response = {"jsonrpc": "2.0", "id": id, "error": error_obj}
```

**Benefits:**
- More readable code for complex data structures
- Consistent with other languages (Python, JavaScript, JSON)
- Reduces need for intermediate variables

**Alternatives Considered:**
- Single-line only (current) - forces awkward splitting into multiple statements
- Builder pattern - too verbose for simple dictionaries

**Impact:**
- Breaking changes: No (feature addition)
- Files affected: All LMS files can now use multiline Dicts
- Related: #1200-1209 (LMS implementation)

**Implementation:**
Modified Dict literal parsing in `src/parser/src/expressions/primary.rs` to skip `Newline` tokens at key positions: after opening brace, before/after colon, after comma, and after values. This allows Dict literals to span multiple lines with arbitrary formatting.

---

### [Stdlib] Comprehensive File I/O API ✅ PARTIALLY IMPLEMENTED

**Type:** Improvement
**Category:** Stdlib
**Priority:** High
**Proposed:** 2025-12-26
**Status:** ✅ Partially Implemented (2026-01-04)

**Implementation:**
Native file I/O functions are now available via extern function declarations:

```simple
# Currently Available ✅
extern fn native_fs_read(path: Str) -> Any      # Read file as byte array
extern fn native_fs_write(path: Str, data: Array[Int]) -> Any  # Write bytes
extern fn native_fs_metadata(path: Str) -> Any  # Get file metadata

# Async file operations
extern fn native_async_file_open(path: Str, mode: Str) -> Any
extern fn native_async_file_read(handle: Any, size: Int) -> Any
extern fn native_async_file_write(handle: Any, data: Array[Int]) -> Any
extern fn native_async_file_close(handle: Any) -> Any
```

**Example:**
```simple
extern fn native_fs_read(path: Str) -> Any
extern fn native_fs_write(path: Str, data: Array[Int]) -> Any

# Read file (returns Ok([bytes...]) or Err(message))
let result = native_fs_read("/path/to/file")

# Write file (data as byte array)
let data = [104, 101, 108, 108, 111, 10]  # "hello\n"
let result = native_fs_write("/tmp/output.txt", data)
```

**Remaining Work:**
- Higher-level wrapper functions (read_file returning String, etc.)
- Directory listing operations
- Path manipulation utilities
- Integration with stdlib module structure

**Files Implemented:**
- `src/runtime/src/value/file_io/file_ops.rs` - Core file operations
- `src/runtime/src/value/file_io/mmap.rs` - Memory-mapped files
- `src/compiler/src/interpreter_call/block_execution.rs` - Extern fn in BDD blocks

---

### [Core] Enhanced String Methods ✅ IMPLEMENTED

**Type:** Improvement
**Category:** API Design
**Priority:** High
**Proposed:** 2025-12-26
**Status:** ✅ Implemented (2026-01-04)

**Implementation:**
Comprehensive string methods are now available in the interpreter. All requested methods work:

```simple
# Substring operations ✅
text.substring(0, 5)      # Extract substring by indices
text.slice(0, 5)          # Alias for substring
text.char_at(0)           # Get character at index
text.at(0)                # Alias for char_at
text.chars()              # List of characters

# Search operations ✅
text.find("pattern")      # Returns Some(index) or None
text.rfind("pattern")     # Find from right
text.index_of("pattern")  # Alias for find
text.contains("sub")      # Check if contains
text.starts_with("pre")   # Check prefix
text.ends_with("suf")     # Check suffix

# Whitespace operations ✅
text.strip()              # Remove leading/trailing whitespace
text.trim()               # Alias for strip
text.trimmed()            # Alias for strip
text.trim_start()         # Remove leading whitespace
text.trim_end()           # Remove trailing whitespace

# Case operations ✅
text.to_upper()           # Uppercase
text.to_lower()           # Lowercase

# Splitting/joining ✅
text.split(",")           # Split by delimiter
text.lines()              # Split by newlines
text.split_lines()        # Alias for lines

# Replacement ✅
text.replace("old", "new")       # Replace first occurrence
text.replace_first("old", "new") # Alias for replace

# Additional methods ✅
text.repeat(3)            # Repeat string n times
text.reverse()            # Reverse string
text.sorted()             # Sort characters
text.take(5)              # First n characters
text.drop(5)              # Skip first n characters
text.pad_left(10, " ")    # Left pad
text.pad_right(10, " ")   # Right pad
text.is_numeric()         # Check if all numeric
text.is_alpha()           # Check if all alphabetic
text.is_alphanumeric()    # Check if alphanumeric
text.is_whitespace()      # Check if all whitespace
text.is_empty()           # Check if empty
text.len()                # String length
text.count("sub")         # Count occurrences
text.parse_int()          # Parse to integer
text.parse_float()        # Parse to float
```

**Files Changed:**
- `src/compiler/src/interpreter_method/string.rs` - All string method implementations

---

### [MCP] JSON Library for Structured Output ✅ IMPLEMENTED

**Type:** Improvement
**Category:** Stdlib
**Priority:** Medium
**Proposed:** 2025-12-26
**Status:** ✅ Implemented (2026-01-05)

**Implementation:**
Full JSON library implemented in `simple/std_lib/src/core/json.spl` (448 lines):

**Features:**
- `JsonValue` enum: Null, Bool, Number, Integer, String, Array, Object
- `JsonParser` class with complete recursive descent parser
- `parse()` function - Parse JSON string to JsonValue
- `stringify()` function - Serialize JsonValue to string
- `stringify_pretty()` function - Pretty-print with indentation
- `JsonBuilder` class with fluent API
- Helper functions: `get_string`, `get_int`, `get_object`, `get_array`

**Example:**
```simple
import core.json

# Parse JSON
result = json.parse("{\"name\": \"alice\", \"age\": 30}")
match result.unwrap():
    case JsonValue.Object(obj):
        print(obj.get("name"))

# Build JSON with builder
s = JsonBuilder.new()
    .set_string("name", "bob")
    .set_int("age", 25)
    .to_string()
# {"name": "bob", "age": 25}

# Serialize manually
val = JsonValue.Object({"key": JsonValue.String("value")})
json.stringify(val)  # {"key": "value"}
```

**Files:**
- Implementation: `simple/std_lib/src/core/json.spl`
- Tests: `simple/std_lib/test/unit/core/json_spec.spl`

---

### [Language] Better Error Handling for Option/Result ✅ IMPLEMENTED

**Type:** Improvement
**Category:** DX
**Priority:** Medium
**Proposed:** 2025-12-26
**Status:** ✅ Implemented (2026-01-05)

**Implementation:**
The `?` operator for Result/Option propagation is fully implemented in parser and interpreter.

**How it works:**
- For `Result[T, E]`: Unwraps `Ok(value)` or early-returns `Err(e)`
- For `Option[T]`: Unwraps `Some(value)` or early-returns `None`

**Example:**
```simple
fn divide(a: i64, b: i64) -> Result[i64, String]:
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

fn compute(a: i64, b: i64, c: i64) -> Result[i64, String]:
    step1 = divide(a, b)?    # Returns Err if b == 0
    step2 = divide(step1, c)?  # Returns Err if c == 0
    return Ok(step2)

# Usage
result = compute(100, 5, 2)  # Ok(10)
result = compute(100, 0, 2)  # Err("division by zero")
```

**Files Changed:**
- Parser: `src/parser/src/expressions/mod.rs:855-858` - `Expr::Try` postfix operator
- Interpreter: `src/compiler/src/interpreter_expr.rs:1383+` - Try expression evaluation
- Error type: `src/compiler/src/error.rs:331` - `CompileError::TryError(Value)`
- Call handling: `src/compiler/src/interpreter_call/core.rs:50,479` - Error propagation

**Tests:**
- Rust tests: `src/driver/tests/interpreter_advanced_features_tests.rs:221-290`
- Simple tests: `simple/std_lib/test/unit/core/try_operator_spec.spl`

**Benefits:**
- Cleaner error handling code
- Encourages proper error propagation
- Familiar to Rust developers
- Reduces boilerplate

---

### [MCP] Symbol Table with Cross-Reference Support

**Type:** Improvement
**Category:** Feature
**Priority:** Low
**Proposed:** 2025-12-26
**Status:** Proposed

**Problem:**
Current MCP parser extracts symbols from single files but doesn't track cross-references (imports, usage, implementations). Limits usefulness for code navigation.

**Proposed Solution:**
Extend MCP parser with symbol table and cross-reference tracking:

```simple
pub class SymbolTable:
    symbols: Dict[String, Symbol]
    references: Dict[String, List[Reference]]

    pub fn add_symbol(symbol: Symbol)
    pub fn add_reference(from: String, to: String, kind: RefKind)
    pub fn find_references(symbol: String) -> List[Reference]
    pub fn find_implementations(trait_name: String) -> List[Symbol]

pub enum RefKind:
    Import
    Call
    Implements
    Inherits
    Uses
```

**Example:**
```simple
# Track cross-references
table = SymbolTable.new()
table.add_symbol(user_class)
table.add_reference("UserService", "User", RefKind.Uses)

# Query
refs = table.find_references("User")
# [Reference(from: "UserService", to: "User", kind: Uses)]
```

**Benefits:**
- Better code navigation in MCP
- Foundation for LSP implementation
- Call graph visualization
- Impact analysis

**Alternatives Considered:**
- LSP-only implementation: MCP should be self-contained
- External symbol database: Prefer in-memory for speed
- No cross-references: Limits MCP usefulness

**Impact:**
- Breaking changes: No (extension)
- Migration path: Opt-in feature
- Implementation: Requires AST walker and scope analysis
