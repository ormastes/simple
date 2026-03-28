# Research: Const Contract, Partial Const, and Meta Const Data

**Date:** 2026-01-21
**Status:** Implementation Complete (Phases 1-3)

## 1. Problem Statement

The user wants compile-time checking for values that are **partially const** - where some parts (like dict keys or format string placeholders) are known at compile time while other parts (values) remain runtime.

### Use Cases

```simple
# Use Case 1: Dict with const keys, runtime values
val config: Dict<const keys=["host", "port"], values=runtime> = {
    "host": get_host(),    # OK - "host" is in const keys
    "port": get_port(),    # OK - "port" is in const keys
    "unknown": "value"     # ERROR - "unknown" not in const keys
}

# Use Case 2: Format string with const placeholders (meta keys)
val template = meta_"Hello {name}, you have {count} messages"
# Now {name} and {count} are known at compile time

# Use Case 3: Instantiation without () when passing dict
val widget = Widget { color: "red", size: 10 }  # instead of Widget({ color: "red", size: 10 })
```

---

## 2. Current State Analysis

### 2.1 Const Support (Limited)

| Feature | Status | Notes |
|---------|--------|-------|
| `const` declarations | Parsed | No HIR lowering (not fully evaluated) |
| Const generic params | Supported | `const N: usize` in generics |
| Const evaluation | None | Only literal values work |
| Dict literal | Parsed | Runtime-only, keys not tracked at compile time |

**Key Gap:** No const evaluation engine exists - constants must be literals.

### 2.2 Type System

The HIR type system has:
- Basic types (`HirType::I64`, `HirType::String`, etc.)
- Generic types (`HirType::Generic`)
- Function types (`HirType::Function`)
- **NO** partial const types or key-constrained dicts

### 2.3 Existing Patterns We Can Build On

1. **i18n Strings** - Compile-time lookup with runtime interpolation:
   ```simple
   Login_"Login failed"      # Name known at compile time
   Welcome_"Hello {user}!"   # Keys (name, {user}) compile-time, value runtime
   ```

2. **Const Generic Parameters** - Already parsed:
   ```simple
   struct Array<T, const N: usize>:
       data: [T; N]
   ```

3. **Where Clauses** - Type constraints at compile time:
   ```simple
   fn process<T>() where T: Clone + Default
   ```

4. **Refinement Types** - Value constraints:
   ```simple
   type PosI64 = i64 where self > 0
   ```

---

## 3. Proposed Design

### 3.1 Partial Const Types

Introduce a **ConstKeys** type modifier for dicts/structs:

```simple
# Option A: Type-level const key constraint
type Config = Dict<String, String> with const_keys("host", "port", "debug")

# Option B: Inline const key declaration
val config: {const "host": String, const "port": i32, *: any} = {
    "host": get_host(),  # Checked at compile time
    "port": 8080,        # Checked at compile time
}

# Option C: Const key set type (preferred - more flexible)
type ConfigKeys = const_keys("host", "port", "debug")
val config: Dict<ConfigKeys, String> = {"host": "localhost"}
```

**Recommended: Option C** - Separates concerns, reusable, composable.

### 3.2 Format Strings with Internal Const Metadata

**Key insight:** Regular format strings already have const keys (the placeholders). The compiler should automatically extract and track these as internal metadata - no special syntax needed.

```simple
# Format string automatically carries const key metadata
val msg = "Hello {name}, count: {count}"
# Internally: FString with const_keys = ["name", "count"]

# When instantiating with a dict, compiler checks keys match
val rendered = msg.format {"name": "Alice", "count": "5"}     # OK
val rendered = msg.format {"name": "Alice"}                    # ERROR: missing "count"
val rendered = msg.format {"name": "Alice", "typo": "5"}      # WARNING: extra key "typo"

# Type signature uses the string's internal const keys
fn render(template: FString, data: Dict<template.keys, String>) -> String:
    # Compiler extracts template.keys at compile time from the format string
    ...
```

**No new syntax** - the existing `"Hello {name}"` format string naturally contains const metadata (the placeholder names). The change is making the compiler **track and validate** these keys.

### 3.3 Dict Instantiation Sugar

Allow struct/class instantiation with just `{ }` when:
1. Constructor takes a single dict parameter
2. Or when using named argument syntax

```simple
# Current
val w = Widget(config: {"color": "red"})

# Proposed - when unambiguous
val w = Widget {"color": "red"}       # Sugar for Widget({...})
val w = Widget {color: "red"}         # Sugar for Widget(color: "red")
```

---

## 4. Grammar Changes Required

### 4.1 New Type Syntax

```ebnf
(* Const key set definition *)
const_keys_type := 'const_keys' '(' string_literal (',' string_literal)* ')'

(* Dict type with const keys *)
constrained_dict_type := 'Dict' '<' const_keys_type ',' type '>'
                       | 'Dict' '<' type ',' type '>' 'with' 'const_keys' '(' string_list ')'

(* Dependent key reference - access const keys from a value *)
dependent_keys := identifier '.keys'

(* Method call with dict - no () needed - ALREADY WORKS *)
(* LBrace is in can_start_argument(), so this parses today: *)
method_with_dict := expression '.' identifier dict_literal

(* Struct/function instantiation sugar - ALREADY WORKS *)
(* func {"key": val} parses as func({"key": val}) *)
struct_instantiation := type_name dict_literal
                      | type_name '(' argument_list ')'
```

### 4.2 Token/AST Changes

```rust
// In token.rs - NO new tokens needed for format strings
// FString already exists and tracks parts

// In ast/nodes/core.rs - enhance FString to expose const keys
pub struct FStringExpr {
    pub span: Span,
    pub parts: Vec<FStringPart>,
    // NEW: Extracted at parse time, always available
    pub const_keys: Vec<String>,  // ["name", "count"] from "Hello {name}, {count}"
}
```

### 4.3 AST Changes

```rust
// In ast/nodes/core.rs

/// Const key set - compile-time known string keys
pub struct ConstKeySet {
    pub span: Span,
    pub keys: Vec<String>,  // Known at compile time
}

/// Extended Type enum
pub enum Type {
    // ... existing variants

    /// Dict with const keys: Dict<const_keys("a", "b"), V>
    ConstKeyDict {
        keys: ConstKeySet,
        value_type: Box<Type>,
    },

    /// Dependent type referencing another value's const keys
    /// Example: Dict<template.keys, String> where template is an FString
    DependentKeys {
        source: String,  // Variable name whose .keys we reference
    },
}

/// FString already exists - just ensure const_keys is populated
/// The parser extracts placeholder names when parsing "{name}" parts
```

---

## 5. Type System Changes

### 5.1 HIR Types

```rust
// In hir/types/type_system.rs

pub enum HirType {
    // ... existing variants

    /// Const key set (compile-time string set)
    ConstKeySet(Vec<String>),

    /// Dict with const keys
    ConstKeyDict {
        keys: Vec<String>,
        value_type: Box<HirType>,
    },

    /// FString type - now carries const key metadata
    FString {
        const_keys: Vec<String>,  // Extracted from "{name}" placeholders
    },

    /// Dependent keys - references another value's const keys
    DependentKeys {
        source_var: String,
    },
}
```

### 5.2 Type Checking Rules

```rust
// Const key dict assignment checking
fn check_const_key_dict_literal(
    expected_keys: &[String],
    actual: &DictLiteral,
) -> Result<(), TypeError> {
    for (key, _value) in &actual.entries {
        // Key must be string literal (not expression)
        let key_str = match key {
            Expr::String(s) => s,
            _ => return Err(TypeError::ConstKeyMustBeLiteral),
        };

        // Key must be in the const key set
        if !expected_keys.contains(key_str) {
            return Err(TypeError::UnknownConstKey {
                key: key_str.clone(),
                expected: expected_keys.clone(),
            });
        }
    }

    // Check all required keys are present
    for required in expected_keys {
        if !actual.entries.iter().any(|(k, _)| matches!(k, Expr::String(s) if s == required)) {
            return Err(TypeError::MissingConstKey {
                key: required.clone(),
            });
        }
    }

    Ok(())
}
```

---

## 6. Compiler Changes

### 6.1 Parser Changes

1. **Lexer** (`src/rust/parser/src/lexer/`):
   - Add `const_keys` keyword
   - Extract placeholder names from FString during lexing (already partially done)

2. **Parser** (`src/rust/parser/src/parser_types.rs`):
   - Parse `const_keys(...)` type expressions
   - Parse `value.keys` dependent key references
   - Parse struct/method call with dict: `Type { ... }`, `obj.method { ... }`
   - Populate `const_keys` field on FString AST nodes

### 6.2 Type Checker Changes

1. **HIR Lowering** (`src/rust/compiler/src/hir/lower/`):
   - Lower const key types
   - Extract and preserve FString const_keys through lowering
   - Validate dict literals against const key constraints
   - Resolve `value.keys` references to actual const key sets

2. **Type Inference** (`src/rust/compiler/src/hir/types/`):
   - Infer const key sets from dict literals
   - Propagate const key constraints through function calls
   - Match FString.const_keys against Dict key constraints

### 6.3 Const Evaluation (New)

Need a const evaluation pass for:
- String literal extraction from `const_keys(...)`
- FString placeholder extraction (already done at parse time)
- Const dict key validation

```rust
// New: src/rust/compiler/src/const_eval/mod.rs

pub enum ConstValue {
    String(String),
    Integer(i64),
    Float(f64),
    Bool(bool),
    StringSet(Vec<String>),  // For const_keys
}

/// Extract const keys from an FString at compile time
pub fn extract_fstring_keys(fstring: &FStringExpr) -> Vec<String> {
    fstring.parts.iter()
        .filter_map(|part| match part {
            FStringPart::Expr(name) => {
                // Extract simple identifier from "{name}"
                // More complex expressions like "{obj.field}" need special handling
                Some(name.clone())
            }
            FStringPart::Literal(_) => None,
        })
        .collect()
}

pub fn eval_const_expr(expr: &Expr) -> Result<ConstValue, ConstEvalError> {
    match expr {
        Expr::String(s) => Ok(ConstValue::String(s.clone())),
        Expr::Integer(n) => Ok(ConstValue::Integer(*n)),
        // ... limited set of const-evaluable expressions
        _ => Err(ConstEvalError::NotConstEvaluable),
    }
}
```

---

## 7. Implementation Phases

### Phase 1: FString Const Keys (Foundation) - IMPLEMENTED

**Status: Complete (2026-01-21)**

1. Created `ConstMeta` module (`src/rust/parser/src/ast/nodes/const_meta.rs`) with:
   - `MetaValue` enum for compile-time values (String, Integer, Float, Bool, StringSet, Dict)
   - `ConstMeta` struct for metadata dictionary
   - `TypeMeta` for type-level metadata (shared by all instances)
   - `ObjMeta` for object-level metadata (instance-specific)
   - `MetaResolver` for lookup: obj meta -> type meta -> default meta
   - `extract_fstring_keys()` helper function

2. Updated `Expr::FString` to struct variant with `type_meta`:
   ```rust
   Expr::FString {
       parts: Vec<FStringPart>,
       type_meta: TypeMeta,  // Contains const_keys
   }
   ```

3. Parser extracts placeholder names during FString parsing (`expressions/primary/literals.rs`)

4. Updated all FString pattern matches across the codebase (15+ files)

### Phase 2: Const Key Sets & Dict - IMPLEMENTED

**Status: Complete (2026-01-21)**

1. Added `Type::ConstKeySet` and `Type::DependentKeys` to AST (`src/rust/parser/src/ast/nodes/core.rs`):
   ```rust
   ConstKeySet { keys: Vec<String> },
   DependentKeys { source: String },
   ```

2. Added parsing for `const_keys("key1", "key2")` in `parser_types.rs`

3. Added `name.keys` syntax for dependent keys in type parser

4. Updated type checker's Type enum in `src/rust/type/src/lib.rs`:
   ```rust
   ConstKeySet { keys: Vec<String> },
   DependentKeys { source: String },
   ```

5. Updated all match handlers in:
   - `doc_gen.rs` (format_type)
   - `checker_unify.rs` (ast_type_to_type, types_compatible, unify)
   - `monomorphize/util.rs` (ast_type_to_concrete)
   - `monomorphize/engine.rs` (substitute_ast_type)

6. Added compile-time dict key validation:
   - `TypeError::ConstKeyNotFound` for unknown keys
   - `TypeError::ConstKeyMissing` for missing required keys
   - `validate_dict_keys_against_const_set()` validation function
   - `validate_dict_const_keys()` in checker_check.rs

### Phase 3: Dependent Keys & FString Integration - IMPLEMENTED

**Status: Complete (2026-01-21)**

1. `value.keys` syntax added to type parser
2. Added `fstring_const_keys: HashMap<String, Vec<String>>` to TypeChecker to track FString const_keys
3. Let statement handler extracts and stores FString const_keys when binding variables
4. `resolve_dependent_keys()` method resolves `template.keys` to the FString's const_keys
5. Dict key validation works with resolved dependent keys

### Phase 4: Instantiation Sugar - ALREADY IMPLEMENTED

**No additional work needed.** The parser already supports dict literals as no-paren arguments:

```simple
# These already work today:
func {"name": "Alice"}           # Parsed as func({"name": "Alice"})
obj.method {"key": "value"}      # Works with method calls too
Widget.create {"color": "red"}   # Static method with dict
```

The `LBrace` token is in `can_start_argument()` (`src/rust/parser/src/expressions/no_paren.rs:177`), enabling dict literals as first argument without parentheses.

---

## 8. Example Code After Implementation

```simple
# ============================================================
# Example 1: Const Key Dict for Config
# ============================================================

# Define allowed config keys
type ConfigKeys = const_keys("host", "port", "debug", "timeout")

# Struct that requires specific keys
struct ServerConfig:
    config: Dict<ConfigKeys, String>

    static fn new(config: Dict<ConfigKeys, String>) -> ServerConfig:
        ServerConfig(config: config)

# Usage - compile-time key checking
val config = ServerConfig {
    "host": "localhost",
    "port": "8080",
    "debug": "true"
}  # OK - all keys valid, no () needed

val bad_config = ServerConfig {
    "host": "localhost",
    "portt": "8080"   # ERROR: "portt" not in ConfigKeys, did you mean "port"?
}

# ============================================================
# Example 2: Format String with Internal Const Keys
# ============================================================

# Regular format string - const keys extracted automatically
val greeting = "Hello {name}, welcome to {place}!"
# Type: FString with const_keys = ["name", "place"]

# Function that uses dependent keys
fn render(template: FString, data: Dict<template.keys, String>) -> String:
    # Compiler knows template.keys from the FString's const metadata
    template.format(data)

# Usage - dict keys validated against format string placeholders
render(greeting, {"name": "Alice", "place": "Wonderland"})  # OK
render(greeting, {"name": "Alice"})                          # ERROR: missing "place"
render(greeting, {"name": "Alice", "typo": "x"})            # WARNING: extra key "typo"

# ============================================================
# Example 3: Method Call with Dict (no parentheses)
# ============================================================

# Instead of: greeting.format({"name": "Alice", "place": "Here"})
val result = greeting.format {"name": "Alice", "place": "Here"}

# Instead of: Widget(config: {"color": "red"})
val widget = Widget {"color": "red", "size": 10}

# ============================================================
# Example 4: Partial Const - Keys const, Values runtime
# ============================================================

fn get_user_data() -> Dict<const_keys("id", "name", "email"), String>:
    # Keys are checked at compile time
    # Values come from runtime (database, user input, etc.)
    {
        "id": fetch_id(),        # OK - "id" in const keys
        "name": fetch_name(),    # OK - "name" in const keys
        "email": fetch_email()   # OK - "email" in const keys
    }

fn process_user(data: Dict<const_keys("id", "name"), String>):
    print "User {data["id"]}: {data["name"]}"

val user = get_user_data()
process_user(user)  # OK - user has "id" and "name" (has extra "email" - OK)
```

---

## 9. Alternatives Considered

### 9.1 TypeScript-style Literal Types
```typescript
type Config = { host: string, port: number }  // Literal object type
```
**Rejected:** Would require significant type system changes.

### 9.2 Dependent Types
```simple
fn process(keys: [String], data: Dict<keys, V>)  // Runtime-dependent
```
**Partially applicable:** Good for advanced use, but overkill for basic const checking.

### 9.3 Macros Only
```simple
@const_keys("host", "port")
val config = {...}
```
**Rejected:** Macros don't integrate with type system.

---

## 10. Conclusion

The proposed design:
1. **FString internal const keys** - Format strings automatically track placeholder names as compile-time metadata (no new syntax)
2. **Const key sets** - Reusable compile-time string sets: `const_keys("a", "b")`
3. **Const key dicts** - Dict types with compile-time key validation: `Dict<const_keys(...), V>`
4. **Dependent keys** - Reference another value's const keys: `Dict<template.keys, String>`
5. **Instantiation sugar** - Omit `()` when passing dict: `Type { ... }`, `obj.method { ... }`

Key requirements:
- Enhance FString AST/HIR to carry `const_keys` extracted from placeholders
- Basic const evaluation for string literal extraction
- New `const_keys(...)` type expression
- Dependent key resolution (`value.keys`)
- Grammar extensions for dict instantiation sugar

**Estimated scope:** Medium - builds on existing patterns (i18n strings, const generics, FString parsing). The key insight is that format strings **already contain** the const key information - we just need to extract and track it through the type system.

**Core principle:** No special `meta_` syntax. Regular `"Hello {name}"` strings carry their placeholder names as internal const metadata that the compiler can validate against.

**Already implemented:** Dict instantiation sugar (`func {"key": val}`) works today - no grammar changes needed for Phase 4.
