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
