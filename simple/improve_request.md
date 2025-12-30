# Improvement Requests

Track improvement ideas discovered while developing Simple standard library and applications.

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
**Status:** Proposed

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
**Status:** Proposed

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
**Status:** Proposed

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
**Status:** Proposed

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

### [Parser] Enum Variant Construction Syntax

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** Proposed

**Problem:**
Enum variant construction syntax `EnumName.Variant(args)` is not parsed correctly.

**Proposed Solution:**
Support qualified enum variant construction with dot notation.

**Example:**
```simple
enum LmsError:
    MethodNotFound(String)
    InvalidParams(String)

let error = LmsError.MethodNotFound("initialize")
```

**Benefits:**
- Enables proper enum usage
- Matches Rust/Swift conventions
- Required for error handling patterns

**Alternatives Considered:**
- Unqualified variants - causes namespace pollution

**Impact:**
- Breaking changes: No (feature addition)
- Files blocked: error.spl, server.spl
- Related: #1200-1209 (LMS implementation)

---

### [Parser] Qualified Method Call Chains

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** Proposed

**Problem:**
Chained method calls like `sys.time.now_ms()` fail with "expected Comma, found Dot".

**Proposed Solution:**
Support multi-level qualified method calls and field access.

**Example:**
```simple
let timestamp = sys.time.now_ms()
let name = session.client_info.name
```

**Benefits:**
- Enables namespace organization
- Required for stdlib module structure
- Natural method chaining

**Alternatives Considered:**
- Flat namespace - causes name conflicts

**Impact:**
- Breaking changes: No (feature addition)
- Files blocked: session.spl, server.spl
- Related: #1200-1209 (LMS implementation)

---

### [Parser] Struct Literal Construction Syntax

**Type:** Improvement
**Category:** Feature
**Priority:** Medium
**Proposed:** 2025-12-25
**Status:** Proposed

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

### [Stdlib] Comprehensive File I/O API

**Type:** Improvement
**Category:** Stdlib
**Priority:** High
**Proposed:** 2025-12-26
**Status:** Proposed

**Problem:**
Current stdlib lacks basic file I/O operations, blocking practical application development. MCP, formatter, linter, and other tools cannot read/write files.

**Proposed Solution:**
Add complete file I/O API to `host.async_nogc_mut.io.fs`:

```simple
# File reading
pub fn read_file(path: String) -> Result[String, IoError]
pub fn read_bytes(path: String) -> Result[List[u8], IoError]
pub fn read_lines(path: String) -> Result[List[String], IoError]

# File writing
pub fn write_file(path: String, content: String) -> Result[(), IoError]
pub fn write_bytes(path: String, data: List[u8]) -> Result[(), IoError]
pub fn append_file(path: String, content: String) -> Result[(), IoError]

# File metadata
pub fn exists(path: String) -> bool
pub fn is_file(path: String) -> bool
pub fn is_dir(path: String) -> bool
pub fn file_size(path: String) -> Result[i64, IoError]

# Directory operations
pub fn list_dir(path: String) -> Result[List[String], IoError]
pub fn create_dir(path: String) -> Result[(), IoError]
pub fn remove_file(path: String) -> Result[(), IoError]
pub fn remove_dir(path: String) -> Result[(), IoError]
```

**Example:**
```simple
use host.async_nogc_mut.io.fs.*

fn main():
    # Read file
    content = read_file("input.spl").unwrap()

    # Process
    processed = process(content)

    # Write file
    write_file("output.txt", processed).unwrap()
```

**Benefits:**
- Enables all self-hosted tools (formatter, linter, MCP, LSP, DAP)
- Makes Simple practical for real applications
- Matches capabilities of other modern languages
- Consistent with existing async I/O design

**Alternatives Considered:**
- FFI to Rust file I/O: Works but not idiomatic Simple
- Synchronous I/O: Conflicts with async design
- Minimal API: Insufficient for practical use

**Impact:**
- Breaking changes: No (new API)
- Migration path: N/A
- Implementation: Wire to existing Rust runtime functions

---

### [Core] Enhanced String Methods

**Type:** Improvement
**Category:** API Design
**Priority:** High
**Proposed:** 2025-12-26
**Status:** Proposed

**Problem:**
String type lacks essential methods for text processing, forcing inefficient workarounds and manual iteration.

**Proposed Solution:**
Add comprehensive string API to `core/string.spl`:

```simple
# Substring operations
pub fn substring(self, start: i64, end: i64) -> String
pub fn substr(self, start: i64, length: i64) -> String
pub fn char_at(self, index: i64) -> String
pub fn chars(self) -> List[String]

# Search operations
pub fn find(self, pattern: String) -> i64  # Returns -1 if not found
pub fn find_all(self, pattern: String) -> List[i64]
pub fn contains(self, pattern: String) -> bool
pub fn starts_with(self, prefix: String) -> bool
pub fn ends_with(self, suffix: String) -> bool

# Whitespace operations
pub fn strip(self) -> String  # Remove leading/trailing whitespace
pub fn lstrip(self) -> String  # Remove leading whitespace
pub fn rstrip(self) -> String  # Remove trailing whitespace

# Case operations
pub fn to_upper(self) -> String
pub fn to_lower(self) -> String
pub fn capitalize(self) -> String

# Splitting/joining
pub fn split(self, delimiter: String) -> List[String]
pub fn join(self, parts: List[String]) -> String
pub fn lines(self) -> List[String]

# Replacement
pub fn replace(self, old: String, new: String) -> String
pub fn replace_all(self, old: String, new: String) -> String
```

**Example:**
```simple
text = "  Hello, World!  "

# Cleanup
clean = text.strip().to_lower()  # "hello, world!"

# Search
pos = clean.find("world")  # 7
has_hello = clean.contains("hello")  # true

# Extract
word = clean.substring(0, 5)  # "hello"
first_char = clean.char_at(0)  # "h"

# Split
words = clean.split(", ")  # ["hello", "world!"]
```

**Benefits:**
- Enables MCP parser implementation
- Matches Python/JavaScript string API familiarity
- Essential for any text processing
- Reduces code complexity

**Alternatives Considered:**
- Regex-based operations: Too heavy for basic operations
- Character iterator only: Too low-level for common tasks
- External string library: Should be in core

**Impact:**
- Breaking changes: No (new methods)
- Migration path: N/A
- Implementation: FFI to Rust string methods or Simple native

---

### [MCP] JSON Library for Structured Output

**Type:** Improvement
**Category:** Stdlib
**Priority:** Medium
**Proposed:** 2025-12-26
**Status:** Proposed

**Problem:**
MCP and other tools need to generate JSON output but must manually construct JSON strings with escape handling. Error-prone and not maintainable.

**Proposed Solution:**
Add JSON library to `core/json.spl`:

```simple
# JSON types
pub enum JsonValue:
    Null
    Bool(bool)
    Number(f64)
    String(String)
    Array(List[JsonValue])
    Object(Dict[String, JsonValue])

# Builder API
pub class JsonBuilder:
    pub fn object() -> JsonObject
    pub fn array() -> JsonArray

pub class JsonObject:
    pub fn set(key: String, value: JsonValue) -> JsonObject
    pub fn build() -> String

pub class JsonArray:
    pub fn add(value: JsonValue) -> JsonArray
    pub fn build() -> String

# Convenience functions
pub fn to_json(value: Any) -> String
pub fn from_json(text: String) -> Result[JsonValue, ParseError]
```

**Example:**
```simple
use core.json.*

# Build JSON
obj = JsonBuilder.object()
    .set("text", JsonValue.String("C> pub class User { … }"))
    .set("mode", JsonValue.String("mcp"))

json_str = obj.build()
# {"text": "C> pub class User { … }", "mode": "mcp"}
```

**Benefits:**
- Type-safe JSON generation
- Automatic escaping
- Cleaner MCP formatter code
- Reusable for LSP, DAP, and other protocols

**Alternatives Considered:**
- Manual string building: Current approach, error-prone
- External JSON library: Should be in stdlib
- Macro-based DSL: Overkill for simple cases

**Impact:**
- Breaking changes: No (new library)
- Migration path: MCP formatter can be simplified
- Implementation: Parser + builder pattern

---

### [Language] Better Error Handling for Option/Result

**Type:** Improvement
**Category:** DX
**Priority:** Medium
**Proposed:** 2025-12-26
**Status:** Proposed

**Problem:**
Current Option/Result handling requires verbose unwrap() calls with potential panics. No convenient way to handle errors inline.

**Proposed Solution:**
Add `?` operator for Result/Option propagation (like Rust):

```simple
# Current verbose approach
fn read_and_process(path: String) -> Result[String, Error]:
    content_result = read_file(path)
    if content_result.is_err():
        return content_result

    content = content_result.unwrap()
    processed = process(content)
    return Ok(processed)

# With ? operator
fn read_and_process(path: String) -> Result[String, Error]:
    content = read_file(path)?  # Auto-propagates error
    processed = process(content)
    return Ok(processed)
```

**Benefits:**
- Cleaner error handling code
- Encourages proper error propagation
- Familiar to Rust developers
- Reduces boilerplate

**Alternatives Considered:**
- Exceptions: Conflicts with effect system
- Monadic bind: Too functional for Simple's style
- Keep verbose: Poor developer experience

**Impact:**
- Breaking changes: No (new syntax)
- Migration path: Optional, verbose form still works
- Implementation: Parser + desugaring to if/return

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
