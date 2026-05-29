# Custom String Literal Suffixes - Language Comparison Research

**Date:** 2026-01-24
**Status:** Research Complete
**Author:** Claude
**Related:** Lexer string suffix support, Value::Unit type

---

## Executive Summary

This document researches how various programming languages support user-definable custom string types via literal syntax. The goal is to inform Simple's implementation of the `"value"_suffix` feature beyond the current `Value::Unit` wrapper.

**Key Finding:** C++ provides the closest model to Simple's existing syntax. Swift, Scala, and JavaScript use alternative approaches (type context, prefix interpolators, tagged templates).

---

## Language Comparison Matrix

| Language | Syntax Style | Position | User-Definable | Compile-Time | Type-Safe |
|----------|-------------|----------|----------------|--------------|-----------|
| **C++** | `"str"_suffix` | Suffix | Yes | Yes | Yes |
| **Swift** | `let x: T = "str"` | Type context | Yes | Yes | Yes |
| **Scala** | `prefix"str"` | Prefix | Yes | Partial | Yes |
| **TypeScript** | `` tag`str` `` | Prefix | Yes | No | Yes |
| **JavaScript** | `` tag`str` `` | Prefix | Yes | No | No |
| **Rust** | `macro!("str")` | Macro | Yes (macros) | Yes | Yes |
| **Python** | `f"str"`, `r"str"` | Prefix | No (built-in only) | No | No |
| **Ruby** | `%q{str}`, `%r{str}` | Prefix | No (built-in only) | No | No |
| **Simple** | `"str"_suffix` | Suffix | **Partial** | No | Partial |

---

## Detailed Language Analysis

### 1. C++ User-Defined Literals (Best Match)

**Syntax:** `"value"_suffix`

**Definition:**
```cpp
// Raw string literal operator
IP operator""_ip(const char* str, std::size_t len) {
    return IP::parse(std::string(str, len));
}

// Numeric literal operator
Distance operator""_km(long double value) {
    return Distance::from_kilometers(value);
}

// Character literal operator
ASCII operator""_ascii(char c) {
    return ASCII(c);
}
```

**Usage:**
```cpp
auto addr = "192.168.1.1"_ip;     // IP type
auto dist = 42.5_km;              // Distance type
auto ch = 'A'_ascii;              // ASCII type
```

**Rules:**
- User-defined suffixes MUST start with `_` (underscore)
- Suffixes without `_` are reserved for standard library
- Cannot contain `__` (double underscore)
- Defined via `operator""` overloading

**Advantages:**
- Compile-time type construction
- Full type safety
- Clean syntax matching Simple's current lexer

**Source:** [cppreference.com - User-defined literals](http://en.cppreference.com/w/cpp/language/user_literal.html)

---

### 2. Swift ExpressibleByStringLiteral

**Syntax:** Type-context based (no suffix)

**Definition:**
```swift
struct IP: ExpressibleByStringLiteral {
    let address: String

    init(stringLiteral value: String) {
        self.address = value
    }
}

struct Regex: ExpressibleByStringLiteral {
    let pattern: String

    init(stringLiteral value: String) {
        self.pattern = value
    }
}
```

**Usage:**
```swift
let ip: IP = "192.168.1.1"           // Type annotation required
let pattern: Regex = "\\d+"          // Type determines conversion

func connect(to ip: IP) { ... }
connect(to: "10.0.0.1")              // Inferred from parameter type
```

**Protocol Hierarchy:**
```
ExpressibleByStringLiteral
    └── ExpressibleByExtendedGraphemeClusterLiteral
            └── ExpressibleByUnicodeScalarLiteral
```

**Related Protocols:**
- `ExpressibleByIntegerLiteral`
- `ExpressibleByFloatLiteral`
- `ExpressibleByArrayLiteral`
- `ExpressibleByDictionaryLiteral`
- `ExpressibleByBooleanLiteral`
- `ExpressibleByNilLiteral`

**Advantages:**
- No special syntax needed
- Works with type inference
- Compile-time validation possible

**Disadvantages:**
- Requires type context (annotation or inference)
- Cannot distinguish between different string-constructible types without context

**Source:** [Apple Developer Documentation](https://developer.apple.com/documentation/swift/expressiblebystringliteral)

---

### 3. Scala String Interpolators

**Syntax:** `prefix"string"` (prefix, not suffix)

**Built-in Interpolators:**
```scala
val name = "Alice"
s"Hello, $name"           // s interpolator: "Hello, Alice"
f"Value: $pi%.2f"         // f interpolator: printf-style formatting
raw"Line1\nLine2"         // raw interpolator: no escape processing
```

**Custom Definition (Scala 3):**
```scala
extension(sc: StringContext)
  def ip(args: Any*): IP =
    val str = sc.parts.mkString
    IP.parse(str)

extension(sc: StringContext)
  def sql(args: Any*): Query =
    // Build parameterized query safely
    Query.build(sc.parts, args)
```

**Usage:**
```scala
val addr = ip"192.168.1.1"
val query = sql"SELECT * FROM users WHERE id = $userId"
```

**How It Works:**
```scala
// Compiler transforms:
ip"192.168.1.1"

// Into:
StringContext("192.168.1.1").ip()
```

**Advantages:**
- Powerful interpolation support
- Can process embedded expressions safely
- Good for DSLs (SQL, GraphQL, etc.)

**Disadvantages:**
- Prefix syntax (different from Simple's suffix)
- Requires extension methods

**Source:** [Scala Documentation - String Interpolation](https://docs.scala-lang.org/scala3/book/string-interpolation.html)

---

### 4. JavaScript/TypeScript Tagged Template Literals

**Syntax:** `` tag`string` `` (prefix with backticks)

**Definition:**
```typescript
// TypeScript with full typing
function ip(strings: TemplateStringsArray, ...values: any[]): IP {
    const raw = strings.raw.join('');
    return new IP(raw);
}

function sql(strings: TemplateStringsArray, ...values: any[]): Query {
    // Safely escape values to prevent SQL injection
    return new Query(strings, values);
}

function html(strings: TemplateStringsArray, ...values: any[]): SafeHTML {
    // Sanitize interpolated values
    return new SafeHTML(strings, values);
}
```

**Usage:**
```typescript
const addr = ip`192.168.1.1`;
const query = sql`SELECT * FROM users WHERE id = ${userId}`;
const content = html`<div>${userInput}</div>`;  // Auto-escaped
```

**Real-World Libraries:**
```typescript
// GraphQL
const query = gql`
  query GetUser($id: ID!) {
    user(id: $id) { name email }
  }
`;

// Styled Components (CSS)
const Button = styled.button`
  background: ${props => props.primary ? 'blue' : 'white'};
  color: ${props => props.primary ? 'white' : 'blue'};
`;

// Lit HTML
const template = html`<div>${content}</div>`;
```

**Advantages:**
- Native language feature
- Full access to raw strings and interpolated values
- Great for DSLs and security (auto-escaping)

**Disadvantages:**
- Prefix syntax with backticks
- Runtime processing (no compile-time)

**Source:** [MDN - Template literals](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Template_literals)

---

### 5. Rust (No Native Suffix Support)

**Approach:** Procedural macros only

```rust
// No native string suffix support
// Must use macros:

// Macro definition (proc_macro crate)
#[proc_macro]
pub fn ip(input: TokenStream) -> TokenStream {
    // Parse and validate at compile time
    let lit: LitStr = parse_macro_input!(input);
    let addr = lit.value();
    // Generate IP construction code
    quote! { IP::new(#addr) }.into()
}

// Usage requires macro syntax
let addr = ip!("192.168.1.1");
```

**Why No Suffix Support:**
- Rust chose not to add user-defined literal suffixes
- Macros provide more power and flexibility
- Avoids complexity in the type system

**Source:** Rust RFC discussions, language design decisions

---

### 6. Python (Built-in Prefixes Only)

**Built-in String Prefixes:**
```python
"hello"              # Regular string
f"Hello, {name}"     # f-string (formatted)
r"raw\nstring"       # Raw string (no escapes)
b"bytes"             # Bytes literal
u"unicode"           # Unicode (Python 2 compat)

# Combinations
rf"raw {formatted}"  # Raw f-string
br"raw bytes"        # Raw bytes
```

**No User-Defined Support:**
- Cannot create custom prefixes like `ip"..."`
- Must use functions: `IP("192.168.1.1")`
- Or factory methods: `IP.from_string("192.168.1.1")`

---

### 7. Ruby (Built-in Percent Literals Only)

**Built-in Percent Literals:**
```ruby
%q{single quoted}     # Like '...'
%Q{double quoted}     # Like "..." with interpolation
%w{word array}        # ['word', 'array']
%i{symbol array}      # [:symbol, :array]
%r{regex}             # Like /regex/
%x{shell command}     # Like `command`
```

**No User-Defined Support:**
- Cannot create custom percent literals
- Must use methods or DSL patterns

---

## Simple Language: Current State

### Lexer Support (Implemented)

```simple
# Already supported by lexer
"192.168.1.1"_ip      # TokenKind::TypedString("192.168.1.1", "ip")
'pattern\d+'_regex    # TokenKind::TypedRawString("pattern\\d+", "regex")
```

### Interpreter Support (Partial)

```rust
// Current implementation (interpreter/expr/literals.rs)
Expr::TypedString(s, suffix) => {
    let family = lookup_unit_family(suffix);
    Ok(Some(Value::Unit {
        value: Box::new(Value::Str(s.clone())),
        suffix: suffix.clone(),
        family: family,
    }))
}
```

**Current Behavior:**
- Creates `Value::Unit` wrapper
- Stores original string + suffix
- Used for unit families (km, hr, etc.)
- Does NOT call user-defined constructors

### Missing Feature

**No way to define custom type constructors:**

```simple
# DESIRED (not yet implemented)
literal fn _ip(s: text) -> IP:
    IP.parse(s)

literal fn _regex(s: text) -> Regex:
    Regex.compile(s)

# Then usage would create actual IP/Regex types:
val addr = "192.168.1.1"_ip    # IP type, not Value::Unit
```

---

## Proposed Design for Simple

### Option A: Trait-Based with Automatic Suffix Mapping (Recommended)

Uses existing trait/mixin system. Suffix automatically maps to type via naming convention.

**Trait Definition:**
```simple
# Core trait for literal conversion
trait FromLiteral<T>:
    static fn from(value: T) -> Self

# Specialized traits for common cases
trait FromText: FromLiteral<text>:
    static fn from(value: text) -> Self

trait FromRawText: FromLiteral<text>:
    static fn from_raw(value: text) -> Self
```

**Type Implementation:**
```simple
class IP:
    octets: List<i32>

    # Implement trait - automatically enables "_ip" suffix
    impl FromText:
        static fn from(value: text) -> IP:
            IP.parse(value)

class Regex:
    pattern: text

    # Implement trait - automatically enables "_regex" suffix
    impl FromRawText:
        static fn from_raw(value: text) -> Regex:
            Regex.compile(value)
```

**Usage:**
```simple
val addr = "192.168.1.1"_ip       # Calls IP.from("192.168.1.1")
val pattern = 'hello\d+'_regex    # Calls Regex.from_raw("hello\\d+")
```

**Suffix → Type Mapping Rules:**

| Suffix | Type Name | Lookup Order |
|--------|-----------|--------------|
| `_ip` | `IP`, `Ip` | 1. Exact case `IP` 2. Title case `Ip` |
| `_regex` | `Regex` | Title case |
| `_json` | `Json`, `JSON` | 1. Title case 2. Upper case |
| `_url` | `Url`, `URL` | 1. Title case 2. Upper case |
| `_my_type` | `MyType` | Snake_case → PascalCase |

**Advantages:**
- No new syntax needed (`literal fn`)
- Uses existing trait system
- Automatic suffix discovery
- Works with Simple's no-overload design

---

### Option B: Explicit `from_xxx` Named Constructors

No trait required. Uses naming convention for typed values.

**Definition:**
```simple
class IP:
    octets: List<i32>

    # Named constructor for text literal
    static fn from_text(value: text) -> IP:
        IP.parse(value)

class Regex:
    pattern: text

    # Named constructor for raw text literal
    static fn from_raw_text(value: text) -> Regex:
        Regex.compile(value)

class Date:
    # Multiple source types
    static fn from_text(value: text) -> Date: ...
    static fn from_timestamp(value: i64) -> Date: ...
```

**Suffix Resolution:**
```simple
"192.168.1.1"_ip      # Looks for IP.from_text()
'pattern'_regex       # Looks for Regex.from_raw_text()
42_date               # Looks for Date.from_i64() or Date.from_timestamp()
```

**Advantages:**
- Simple, no traits needed
- Explicit and discoverable
- Works with existing method system

**Disadvantages:**
- No compile-time trait check
- Must follow naming convention exactly

---

### Option C: C++ Style `literal fn` (Explicit Registration)

**Syntax:**
```simple
# Explicit literal function definition
literal fn _ip(value: text) -> IP:
    IP.parse(value)

literal fn _regex(value: text) -> Regex:
    Regex.compile(value)

# Usage
val addr = "192.168.1.1"_ip
val pattern = 'hello\d+'_regex
```

**Advantages:**
- Most explicit
- Similar to C++ (well-understood)
- Full control over conversion

**Disadvantages:**
- New syntax (`literal fn`)
- Separate from type definition
- Not discoverable from type

---

### Option D: Swift Style (Type Context Only)

**Syntax:**
```simple
# Definition via trait
impl IP: FromStringLiteral:
    static fn from_literal(s: text) -> IP:
        IP.parse(s)

# Usage (requires type annotation)
val addr: IP = "192.168.1.1"
```

**Advantages:**
- No special suffix syntax
- Works with type inference

**Disadvantages:**
- Loses explicit suffix syntax
- Requires type context always
- Cannot mix types in expression

---

## Suffix Display and Notation

### How Suffixes Are Shown

| Context | Display | Example |
|---------|---------|---------|
| Source code | `"value"_suffix` | `"192.168.1.1"_ip` |
| Error messages | `text_suffix` or `TypeName` | `text_ip` or `IP` |
| Type signature | `TypeName` | `fn connect(addr: IP)` |
| REPL/Debug | `TypeName("value")` | `IP("192.168.1.1")` |

### Suffix Naming Convention

```simple
# Suffix to Type mapping
_ip       → IP, Ip
_url      → URL, Url
_regex    → Regex
_json     → JSON, Json
_uuid     → UUID, Uuid
_path     → Path
_date     → Date
_time     → Time
_duration → Duration

# Multi-word suffixes (snake_case → PascalCase)
_ip_addr     → IpAddr, IPAddr
_file_path   → FilePath
_mime_type   → MimeType
_http_method → HttpMethod, HTTPMethod
```

---

## Grammar Comparison and Pitfalls

### Grammar A: Trait-Based (Recommended)

```ebnf
(* No new grammar - uses existing trait syntax *)
trait_impl     ::= "impl" type_name ":" trait_name ":" NEWLINE INDENT method_def+ DEDENT
method_def     ::= "static" "fn" "from" "(" param ")" "->" type_name ":" body

(* Typed string literal - already in lexer *)
typed_string   ::= STRING "_" IDENTIFIER
typed_raw_str  ::= RAW_STRING "_" IDENTIFIER
```

**Pitfalls:**
- Suffix must match type name (convention-based)
- Ambiguity if multiple types have similar names
- Import required to bring type into scope

**Mitigation:**
```simple
# Explicit suffix registration (optional)
@literal_suffix("ip")
class IP: ...

# Or use module-qualified lookup
"192.168.1.1"_net.ip   # Looks for net.IP.from()
```

---

### Grammar B: Named Constructor

```ebnf
(* No new grammar - uses existing static fn syntax *)
static_method  ::= "static" "fn" method_name "(" params ")" "->" type_name ":" body
method_name    ::= "from_" type_suffix    (* from_text, from_raw_text, from_i64 *)

(* Typed string literal - already in lexer *)
typed_string   ::= STRING "_" IDENTIFIER
```

**Pitfalls:**
- Method name must exactly match convention
- No compile-time verification of convention
- Easy to misspell `from_text` vs `from_txt`

**Mitigation:**
```simple
# Lint rule to verify from_* methods
# lint: from_constructor_naming
```

---

### Grammar C: Explicit `literal fn`

```ebnf
(* NEW grammar element *)
literal_fn_def ::= "literal" "fn" "_" IDENTIFIER "(" param ")" "->" type_name ":" body

(* Example *)
literal_fn_def ::= "literal" "fn" "_ip" "(" "value" ":" "text" ")" "->" "IP" ":" body
```

**Pitfalls:**
- New keyword `literal`
- Separate from type definition (scattered code)
- Must be in scope where literal is used

**Mitigation:**
```simple
# Auto-export literal functions with type
pub class IP: ...
pub literal fn _ip(s: text) -> IP: ...  # Exported together
```

---

### Grammar D: Attribute-Based Registration

```ebnf
(* Uses attribute syntax *)
attr_literal   ::= "@" "literal" "(" STRING ")" NEWLINE class_or_fn_def

(* Example *)
attr_literal   ::= "@literal(\"ip\")" NEWLINE "class" "IP" ":" ...
```

**Example:**
```simple
@literal("ip")
class IP:
    impl FromText:
        static fn from(value: text) -> IP:
            IP.parse(value)

# Or on method directly
class IP:
    @literal("ip")
    static fn from_text(value: text) -> IP:
        IP.parse(value)
```

**Pitfalls:**
- Requires attribute processing
- String literal for suffix name (not type-checked)

---

## Pitfall Summary

| Approach | Main Pitfall | Severity | Mitigation |
|----------|-------------|----------|------------|
| **Trait-based** | Suffix ↔ Type name mismatch | Medium | Lint + `@literal_suffix` |
| **Named constructor** | Convention typos | Medium | Lint rule |
| **`literal fn`** | Scattered definitions | Low | Co-locate with type |
| **Attribute-based** | String not type-checked | Low | IDE support |

### Common Pitfalls (All Approaches)

1. **Scope Issues:**
   ```simple
   # IP not imported - what happens?
   val addr = "192.168.1.1"_ip    # Error or Value::Unit?
   ```
   **Solution:** Error if type not in scope, suggest import.

2. **Ambiguous Suffixes:**
   ```simple
   # Both modules define IP
   use network.IP
   use custom.IP
   val addr = "..."_ip    # Which IP?
   ```
   **Solution:** Require qualified suffix `_network.ip` or error.

3. **Raw vs Regular String:**
   ```simple
   "hello\n"_regex    # Escaped newline
   'hello\n'_regex    # Literal backslash-n
   ```
   **Solution:** Different trait methods `from()` vs `from_raw()`.

4. **Validation Errors:**
   ```simple
   val bad = "not-an-ip"_ip    # Runtime or compile-time error?
   ```
   **Solution:**
   - Runtime: Return `Result<IP, Error>` or panic
   - Compile-time: Only for const literals (future)

---

## Recommended Design: Option A (Trait-Based)

### Final Syntax

```simple
# 1. Define trait (in std library)
trait FromLiteral<T>:
    """Enables "value"_suffix literal syntax."""
    static fn from(value: T) -> Self

# 2. Implement for your type
class IP:
    octets: List<i32>

    impl FromLiteral<text>:
        static fn from(value: text) -> IP:
            match IP.parse(value):
                Ok(ip): ip
                Err(e): panic("Invalid IP literal: {value}")

# 3. Use with suffix (type name lowercase = suffix)
val addr = "192.168.1.1"_ip

# 4. Optional: Custom suffix name
@literal_suffix("ipv4")
class IP:
    impl FromLiteral<text>: ...

val addr = "192.168.1.1"_ipv4
```

### Resolution Algorithm

```
1. Parse "value"_suffix
2. Convert suffix to type name:
   - _ip → IP, Ip
   - _my_type → MyType
3. Look up type in current scope
4. Check if type implements FromLiteral<text>
5. If raw string ('...'_suffix), check FromLiteral<raw_text>
6. Call Type.from(value)
7. Return result
```

---

---

## Implementation Plan

### Phase 1: Core Trait Definition

```simple
# std/literal.spl

trait FromLiteral<T>:
    """
    Enables typed string literal syntax: "value"_suffix

    Implement this trait to allow your type to be constructed
    from string literals with a type suffix.
    """
    static fn from(value: T) -> Self

# Convenience aliases
trait FromText: FromLiteral<text>
trait FromRawText: FromLiteral<text>  # For raw strings
```

### Phase 2: Suffix Resolution in Interpreter

```rust
// interpreter/expr/literals.rs
Expr::TypedString(s, suffix) => {
    // 1. Convert suffix to type name
    let type_name = suffix_to_type_name(suffix);  // "ip" → "IP"

    // 2. Look up type in scope
    let ty = self.resolve_type(&type_name)?;

    // 3. Check if implements FromLiteral<text>
    if ty.implements_trait("FromLiteral", &["text"]) {
        // 4. Call Type.from(s)
        self.call_static_method(&ty, "from", vec![Value::Str(s)])
    } else {
        // Fallback to Value::Unit (backward compat)
        Ok(Value::Unit { value: s, suffix })
    }
}
```

### Phase 3: Standard Library Types

```simple
# std/net/ip.spl
class IP:
    octets: List<i32>

    impl FromLiteral<text>:
        static fn from(value: text) -> IP:
            IP.parse(value).unwrap_or_panic("Invalid IP: {value}")

# std/regex.spl
class Regex:
    pattern: text
    compiled: RegexInternal

    impl FromLiteral<text>:
        static fn from(value: text) -> Regex:
            Regex.compile(value).unwrap_or_panic("Invalid regex: {value}")

# std/url.spl
class URL:
    impl FromLiteral<text>:
        static fn from(value: text) -> URL:
            URL.parse(value).unwrap_or_panic("Invalid URL: {value}")

# std/path.spl
class Path:
    impl FromLiteral<text>:
        static fn from(value: text) -> Path:
            Path.new(value)

# std/json.spl
class Json:
    impl FromLiteral<text>:
        static fn from(value: text) -> Json:
            Json.parse(value).unwrap_or_panic("Invalid JSON: {value}")

# std/uuid.spl
class UUID:
    impl FromLiteral<text>:
        static fn from(value: text) -> UUID:
            UUID.parse(value).unwrap_or_panic("Invalid UUID: {value}")
```

### Phase 4: Raw String Support

```simple
# Different trait for raw strings (single quotes)
trait FromRawLiteral<T>:
    static fn from_raw(value: T) -> Self

class Regex:
    # Regular string: "hello\\d+" (escaped)
    impl FromLiteral<text>:
        static fn from(value: text) -> Regex:
            Regex.compile(value)

    # Raw string: 'hello\d+' (literal backslash)
    impl FromRawLiteral<text>:
        static fn from_raw(value: text) -> Regex:
            Regex.compile(value)

# Usage
val r1 = "hello\\d+"_regex   # FromLiteral.from()
val r2 = 'hello\d+'_regex    # FromRawLiteral.from_raw()
```

### Phase 5: Optional Custom Suffix Attribute

```simple
# When type name doesn't match desired suffix
@literal_suffix("ipv4")
class IP:
    impl FromLiteral<text>: ...

# Now both work:
val a = "192.168.1.1"_ip      # Default (type name)
val b = "192.168.1.1"_ipv4    # Custom suffix
```

### Phase 6: Compile-Time Validation (Future)

```simple
# Mark as compile-time evaluable
@const
impl FromLiteral<text> for IP:
    static fn from(value: text) -> IP:
        # Validated at compile time for const literals
        IP.parse(value).unwrap()

# Compile-time error for invalid literal
val bad = "not-an-ip"_ip    # ERROR at compile time
```

---

## Security Considerations

1. **Injection Prevention:** Literal functions can validate/sanitize input
2. **Compile-Time Checks:** Invalid literals caught early
3. **Type Safety:** Return type enforced by type system

---

## References

1. [C++ User-Defined Literals](http://en.cppreference.com/w/cpp/language/user_literal.html)
2. [Swift ExpressibleByStringLiteral](https://developer.apple.com/documentation/swift/expressiblebystringliteral)
3. [Scala String Interpolation](https://docs.scala-lang.org/scala3/book/string-interpolation.html)
4. [MDN Template Literals](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Template_literals)
5. [TypeScript Template Literal Types](https://www.typescriptlang.org/docs/handbook/2/template-literal-types.html)

---

## Conclusion

**Recommendation:** Implement **Option A (Trait-Based)** with `FromLiteral<T>` trait.

### Why Trait-Based?

| Criteria | Trait-Based | `literal fn` | Named Constructor |
|----------|-------------|--------------|-------------------|
| Uses existing syntax | Yes | No (new keyword) | Yes |
| Co-located with type | Yes | No | Yes |
| Discoverable | Yes (trait) | No | Partial |
| Type-safe | Yes | Yes | No |
| Works with no-overload | Yes | Yes | Yes |
| IDE support | Easy | Needs work | Easy |

### Summary

```simple
# Define once with type
class IP:
    impl FromLiteral<text>:
        static fn from(value: text) -> IP:
            IP.parse(value).unwrap()

# Use anywhere
val addr = "192.168.1.1"_ip    # Automatic!
```

### Benefits

1. **No new syntax** - uses existing trait system
2. **Automatic suffix mapping** - `_ip` → `IP.from()`
3. **Type-safe** - trait must be implemented
4. **Discoverable** - IDE can show all `FromLiteral` implementors
5. **Backward compatible** - falls back to `Value::Unit` if no trait

**Priority:** Medium - Useful feature, enables cleaner APIs

**Dependencies:**
- Trait system must support static methods
- Suffix → type name resolution in interpreter

---

## Implementation Status (2026-01-24)

### Implemented Features

The following features have been implemented:

#### 1. Suffix → Type Name Conversion

**File:** `src/rust/compiler/src/interpreter/expr/units.rs`

```rust
pub(crate) fn suffix_to_type_names(suffix: &str) -> Vec<String> {
    // "ip" → ["IP", "Ip"]  (short suffixes try UPPERCASE first)
    // "my_type" → ["MyType"]  (snake_case → PascalCase)
    // "regex" → ["Regex"]  (longer suffixes use PascalCase)
}
```

#### 2. Static `from()` Method Lookup

**File:** `src/rust/compiler/src/interpreter/expr/literals.rs`

When evaluating `Expr::TypedString(s, suffix)`:
1. Convert suffix to type names using `suffix_to_type_names()`
2. Look up type in `classes` HashMap
3. Find static `from(text)` method on the class
4. Call `Type.from(s)` and return the result
5. Fall back to `Value::Unit` if no matching type/method found

#### 3. `literal fn` Syntax (Explicit Override)

**New Token:** `TokenKind::Literal` for the `literal` keyword

**New AST Node:** `LiteralFunctionDef`
```rust
pub struct LiteralFunctionDef {
    pub span: Span,
    pub suffix: String,        // "re" for _re
    pub param_name: String,
    pub return_type: Option<Type>,
    pub body: Block,
}
```

**New Node Variant:** `Node::LiteralFunction(LiteralFunctionDef)`

**Registry:** Thread-local `LITERAL_FUNCTIONS` HashMap
```rust
thread_local! {
    pub(crate) static LITERAL_FUNCTIONS: RefCell<HashMap<String, LiteralFunctionInfo>> = RefCell::new(HashMap::new());
}
```

#### 4. Resolution Order

```
"192.168.1.1"_ip
    ↓
1. Check LITERAL_FUNCTIONS registry (explicit override)
    ↓
2. Convert suffix → type names: "ip" → ["IP", "Ip"]
    ↓
3. Look up type in classes HashMap
    ↓
4. Check for static from(text) method
    ↓
5. Call Type.from(value) → return result
    ↓
   (fallback) Create Value::Unit { value, suffix, family }
```

### Usage Examples

```simple
# Define a class with static from() method
class IP:
    value: text

    static fn from(s: text) -> IP:
        IP(value: s)

# Use suffix - automatically calls IP.from()
val addr = "192.168.1.1"_ip
print addr.value  # Output: 192.168.1.1

# Snake_case suffix → PascalCase type
class MyType:
    data: text
    static fn from(s: text) -> MyType:
        MyType(data: s)

val obj = "hello"_my_type
print obj.data  # Output: hello

# Explicit override with literal fn
class Regex:
    pattern: text
    static fn compile(p: text) -> Regex:
        Regex(pattern: "compiled:" + p)

literal fn _re(s: text) -> Regex:
    Regex.compile(s)

val pattern = "test"_re
print pattern.pattern  # Output: compiled:test
```

### Test Coverage

**File:** `test/lib/std/unit/core/custom_literals_spec.spl`

- 8 passing tests covering:
  - `_ip` → `IP.from()` mapping
  - Snake_case suffix → PascalCase type conversion
  - Short suffixes (≤3 chars) try UPPERCASE first
  - Longer suffixes use PascalCase only
  - Case-sensitive suffix matching

### Known Limitations

1. **`literal fn` inside test blocks:** The `literal fn` registration happens during block evaluation, so it must be defined before the test block runs. Define `literal fn` at module level for reliable behavior.

2. **No compile-time validation:** Invalid suffixes (no matching type) fall back to `Value::Unit` at runtime.

3. **No `from_raw()` for raw strings:** Currently both `"..."_suffix` and `'...'_suffix` call `from()`. A future enhancement could add `from_raw()` for raw string literals.
