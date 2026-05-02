# Type Conversion Systems - Existing Infrastructure

**Date:** 2026-02-04
**Status:** ✅ Comprehensive conversion infrastructure exists
**Finding:** Multiple conversion systems already implemented in Simple

## Summary

Simple has **extensive type conversion infrastructure** already implemented. Multiple conversion systems exist for different purposes:

1. **AST Conversion** (Parse tree → Interpreter AST)
2. **FFI Type Mapping** (Simple types ↔ Rust types)
3. **Runtime Value Conversion** (Primitive type conversions)
4. **FFI Specs** (Conversion function specifications)

## 1. AST Conversion Modules

**Location:** `src/app/interpreter/ast_convert*.spl`

Converts parse tree (CST) to interpreter AST for execution.

### Files

| File | Lines | Purpose |
|------|-------|---------|
| `ast_convert.spl` | 129 | Top-level module conversion |
| `ast_convert_expr.spl` | 556 | Expression conversion |
| `ast_convert_stmt.spl` | 577 | Statement conversion |
| `ast_convert_pattern.spl` | 163 | Pattern conversion |

**Total:** 1,425 lines of AST conversion code

### Functionality

```simple
# Convert parse tree to module
fn tree_to_module(tree: Tree) -> Result<Module, String>

# Convert individual nodes
fn convert_statement(tree: &Tree, node: Node) -> Result<Statement, String>
fn convert_expression(tree: &Tree, node: Node) -> Result<Expression, String>
fn convert_pattern(tree: &Tree, node: Node) -> Result<Pattern, String>
```

**Handles:**
- ✅ All statement types (let, if, match, for, while, etc.)
- ✅ All expression types (binary ops, calls, literals, etc.)
- ✅ All pattern types (literal, struct, enum, array, etc.)
- ✅ Function definitions, classes, structs, enums
- ✅ Import statements
- ✅ Type annotations

**Example:**
```simple
import interpreter.ast_convert

val tree = parser.parse("fn main(): print 'Hello'")
val module = tree_to_module(tree)  # Returns Module AST
```

## 2. FFI Type Mapping

**Location:** `src/app/ffi_gen/type_mapping.spl`

Maps between Simple types and Rust types for FFI code generation.

### Functions

```simple
# Simple type → Rust type
fn simple_to_rust(simple_type: text) -> text

# Simple type → C ABI type
fn simple_to_c_abi(simple_type: text) -> text

# Rust type → FFI wrapper type
fn rust_to_ffi(rust_type: text) -> text
```

### Type Mappings

| Simple Type | Rust Type | C ABI Type |
|-------------|-----------|------------|
| `i32` | `i32` | `i32` |
| `i64` | `i64` | `i64` |
| `f32` | `f32` | `f32` |
| `f64` | `f64` | `f64` |
| `bool` | `bool` | `bool` |
| `text` | `String` | `*const c_char` |
| `()` | `()` | `()` |
| `Option<T>` | `Option<T>` | `*mut T` (nullable) |
| `[T]` | `Vec<T>` | `*mut T, usize` |

### Advanced Mappings

**Handles:**
- ✅ Generic types: `Option<i32>` → `Option<i32>`
- ✅ Arrays: `[text]` → `Vec<String>`
- ✅ Tuples: `(i32, text)` → `(i32, String)`
- ✅ Custom types: `MyClass` → `MyClass` (opaque handle)

**Example:**
```simple
import ffi_gen.type_mapping

val rust_type = simple_to_rust("Option<[text]>")
# Returns: "Option<Vec<String>>"

val c_type = simple_to_c_abi("text")
# Returns: "*const c_char"
```

## 3. Runtime Value Conversion

**Location:** `src/app/interpreter.extern/conversion.spl`

Converts between runtime values (int, string, bool, float).

### Functions

```simple
# Type conversions
fn to_string_extern(args: [Value]) -> Result<Value, InterpreterError>
fn to_int_extern(args: [Value]) -> Result<Value, InterpreterError>
fn to_float_extern(args: [Value]) -> Result<Value, InterpreterError>
fn to_bool_extern(args: [Value]) -> Result<Value, InterpreterError>

# Type checking
fn type_of_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_int_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_float_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_string_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_bool_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_nil_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_array_extern(args: [Value]) -> Result<Value, InterpreterError>
fn is_dict_extern(args: [Value]) -> Result<Value, InterpreterError>
```

### Conversion Rules

**to_int:**
- `Int` → `Int` (identity)
- `Float` → `Int` (truncate)
- `String` → `Int` (parse)
- `Bool` → `Int` (true=1, false=0)

**to_float:**
- `Float` → `Float` (identity)
- `Int` → `Float` (cast)
- `String` → `Float` (parse)
- `Bool` → `Float` (true=1.0, false=0.0)

**to_string:**
- Any type → `String` (display representation)

**to_bool:**
- `Bool` → `Bool` (identity)
- `Int` → `Bool` (0=false, non-zero=true)
- `String` → `Bool` (empty=false, non-empty=true)
- `nil` → `Bool` (false)
- Arrays/Dicts → `Bool` (empty=false, non-empty=true)

## 4. RuntimeValue Tagged Pointer

**Location:** `src/lib/runtime_value.spl`

Efficient value representation using tag bits (no allocation for primitives).

### Architecture

```
┌─────────────────────────────────────────────────────────┬─────┐
│                 61 bits payload                          │ 3   │
│                                                          │bits │
└─────────────────────────────────────────────────────────┴─────┘
```

**Tag Encoding:**
- `0b000`: Heap pointer (objects, strings, arrays)
- `0b001`: Immediate integer (61-bit signed)
- `0b010`: Float (NaN-boxing)
- `0b011`: Bool (false=0, true=1 in bit 3)
- `0b100`: Nil

### API

```simple
class RuntimeValue:
    # Constructors
    static fn from_int(n: i64) -> RuntimeValue
    static fn from_float(f: f64) -> RuntimeValue
    static fn from_bool(b: bool) -> RuntimeValue
    static fn nil() -> RuntimeValue
    static fn from_ptr(ptr: *mut Object) -> RuntimeValue

    # Type checking
    fn is_int() -> bool
    fn is_float() -> bool
    fn is_bool() -> bool
    fn is_nil() -> bool
    fn is_ptr() -> bool

    # Value extraction
    fn as_int() -> Option<i64>
    fn as_float() -> Option<f64>
    fn as_bool() -> Option<bool>
    fn as_ptr() -> Option<*mut Object>
```

## 5. FFI Conversion Specs

**Location:** `src/app/ffi_gen.specs/conversion.spl`

Specifications for generating conversion FFI wrappers.

### Spec Format

```simple
InternFnSpec(
    name: "to_string",
    category: "conversion",
    params: [InternParamSpec(name: "value", value_type: "Value")],
    return_type: "String",
    runtime_fn: "",
    doc: "Convert any value to string representation"
)
```

**Generates:**
```rust
#[no_mangle]
pub extern "C" fn rt_to_string(value: *mut RuntimeValue) -> *mut c_char {
    // Generated FFI wrapper
}
```

## Existing Conversion Patterns

### Pattern 1: Parse Tree → AST
```simple
import interpreter.ast_convert

val tree = parser.parse(source)
val ast = tree_to_module(tree)?
```

### Pattern 2: Simple Type → Rust Type
```simple
import ffi_gen.type_mapping

val rust_type = simple_to_rust("Option<[text]>")
# "Option<Vec<String>>"
```

### Pattern 3: Runtime Value Conversion
```simple
import interpreter.extern.conversion

val string_val = to_string_extern([value])?
val int_val = to_int_extern([value])?
```

### Pattern 4: Tagged Pointer
```simple
import std.runtime_value

val val1 = RuntimeValue.from_int(42)
val val2 = RuntimeValue.from_float(3.14)
val val3 = RuntimeValue.from_bool(true)

if val1.is_int():
    print val1.as_int()  # Some(42)
```

## What's Missing for Parser FFI

### ✅ Already Exists

1. **AST conversion infrastructure** - Comprehensive (1,425 lines)
2. **Type mapping** - Simple ↔ Rust conversion
3. **Runtime value handling** - Tagged pointers
4. **FFI code generation** - Automated wrapper generation

### ❌ Still Needed for Parser FFI

1. **Parser FFI functions** - Entry points for Rust to call
   ```simple
   fn rt_parse_file(path: text) -> RuntimeValue
   fn rt_parse_expr(source: text) -> RuntimeValue
   fn rt_lex_tokens(source: text) -> RuntimeValue
   ```

2. **AST → RuntimeValue conversion** - Serialize AST to RuntimeValue
   ```simple
   fn ast_to_runtime_value(ast: Module) -> RuntimeValue
   ```

3. **RuntimeValue → Rust AST conversion** - Deserialize in Rust
   ```rust
   fn runtime_value_to_ast(value: &RuntimeValue) -> Result<AstNode>
   ```

## Recommended Approach

### Option A: Direct RuntimeValue Bridge

Use existing RuntimeValue infrastructure:

```simple
# In Simple (src/app/io/mod.spl or new file)
extern fn rt_parse_file(path: text) -> RuntimeValue:
    import compiler.parser
    val ast = parser.parse_file(path)
    ast_to_runtime_value(ast)  # NEW: Convert AST to RuntimeValue

fn ast_to_runtime_value(ast: Module) -> RuntimeValue:
    # Serialize AST as nested RuntimeValue structures
    RuntimeValue.from_dict({
        "type": "Module",
        "statements": ast.statements.map(stmt_to_runtime_value),
        "imports": ast.imports.map(import_to_runtime_value),
    })
```

```rust
// In Rust (rust/compiler/src/parser_ffi.rs)
extern "C" {
    fn rt_parse_file(path: *const c_char) -> *mut RuntimeValue;
}

pub fn parse_file(path: &str) -> Result<Module> {
    let c_path = CString::new(path)?;
    let value = unsafe { rt_parse_file(c_path.as_ptr()) };
    runtime_value_to_module(value)  // NEW: Deserialize RuntimeValue to Module
}
```

### Option B: JSON Serialization Bridge

Simpler but slower:

```simple
extern fn rt_parse_file_json(path: text) -> text:
    import compiler.parser
    val ast = parser.parse_file(path)
    ast.to_json()  # Serialize to JSON string
```

```rust
pub fn parse_file(path: &str) -> Result<Module> {
    let json = unsafe { rt_parse_file_json(path) };
    serde_json::from_str(&json)  // Deserialize JSON to Module
}
```

### Option C: Shared Memory Buffer

Fastest but most complex:

```simple
extern fn rt_parse_file_binary(path: text, buffer: *mut u8, size: usize) -> usize:
    import compiler.parser
    val ast = parser.parse_file(path)
    serialize_ast_binary(ast, buffer, size)  # Binary serialization
```

## Code Reuse Opportunities

### 1. Use Existing AST Conversion

The `ast_convert*.spl` modules already do Parse Tree → AST.
Just need to add AST → RuntimeValue serialization.

### 2. Use Existing Type Mapping

The `type_mapping.spl` already maps Simple → Rust types.
Can reuse for FFI function signatures.

### 3. Use Existing RuntimeValue

The `runtime_value.spl` provides efficient value representation.
No need to create new serialization format.

## Effort Estimate

### Minimal Approach (Option B - JSON)

- ✅ **AST → JSON serialization:** ~200 lines (derive Serialize)
- ✅ **Rust JSON deserialization:** ~100 lines (derive Deserialize)
- ✅ **FFI wrapper functions:** ~50 lines
- **Total:** ~350 lines, **1 day of work**

### Recommended Approach (Option A - RuntimeValue)

- **AST → RuntimeValue conversion:** ~400 lines
- **RuntimeValue → Rust AST conversion:** ~400 lines
- **FFI wrapper functions:** ~100 lines
- **Total:** ~900 lines, **2-3 days of work**

### Optimal Approach (Option C - Binary)

- **Binary AST serialization:** ~800 lines
- **Binary deserialization in Rust:** ~800 lines
- **FFI wrapper functions:** ~100 lines
- **Total:** ~1,700 lines, **5-7 days of work**

## Recommendation

**Use Option A (RuntimeValue bridge):**

1. **Reuse existing infrastructure:**
   - RuntimeValue tagged pointers
   - AST conversion modules
   - Type mapping functions

2. **Reasonable performance:**
   - Better than JSON (no string parsing)
   - Worse than binary (more allocations)
   - Acceptable for compile-time parsing

3. **Type-safe:**
   - RuntimeValue is already well-tested
   - Minimal new code needed
   - Clear error handling

## Implementation Checklist

- [ ] Create `src/app/parser_ffi.spl` module
- [ ] Implement `ast_to_runtime_value()` functions
- [ ] Add `rt_parse_file()`, `rt_parse_expr()`, `rt_lex_tokens()` externs
- [ ] Create `rust/compiler/src/parser_ffi.rs`
- [ ] Implement `runtime_value_to_ast()` conversion in Rust
- [ ] Add FFI wrapper functions in Rust
- [ ] Update 260+ Rust files to use new FFI
- [ ] Test and validate

## Related Files

- **AST conversion:** `src/app/interpreter/ast_convert*.spl`
- **Type mapping:** `src/app/ffi_gen/type_mapping.spl`
- **Runtime values:** `src/lib/runtime_value.spl`
- **Conversion specs:** `src/app/ffi_gen.specs/conversion.spl`
- **FFI generation:** `src/app/ffi_gen/rust_codegen.spl`

## Conclusion

✅ **Extensive type conversion infrastructure already exists**

The Simple codebase has:
- 1,425 lines of AST conversion code
- 115 lines of FFI type mapping
- 107 lines of runtime value conversion
- Complete RuntimeValue tagged pointer system
- FFI code generation framework

**Only missing:**
- Parser-specific FFI entry points (~100 lines)
- AST ↔ RuntimeValue serialization (~800 lines)

**Total new code needed:** ~900 lines (2-3 days of work)

**Recommendation:** Use RuntimeValue bridge (Option A) to leverage existing infrastructure.
