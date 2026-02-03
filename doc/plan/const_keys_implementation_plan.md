# Const Keys Implementation Plan

**Date:** 2026-02-03
**Phase:** 8 of Rust Feature Parity Roadmap
**Total Time:** 6 hours
**Status:** Planning

---

## Overview

Implement compile-time key validation for format strings (templates), ensuring that all required keys are provided and no extra keys exist. This prevents runtime errors from missing or typo'd keys.

**Key Concept:**
```simple
val template = "Hello {name}, you are {age} years old"
val greeting = template.with({"name": "Alice", "age": 30})  # OK

val bad = template.with({"name": "Bob"})  # ERROR: missing key "age"
val typo = template.with({"name": "Charlie", "ag": 25})  # ERROR: unknown key "ag", missing "age"
```

---

## Background: Const Keys

### Definition

**Const Keys** are compile-time known keys extracted from string templates. The compiler tracks which keys are required and validates that `.with()` calls provide exactly those keys.

### Why Const Keys Matter

**Safety:**
```simple
# Without const keys (runtime error):
val template = "User {name} has {points} points"
val msg = template.with({"name": "Alice"})  # Runtime error: missing "points"

# With const keys (compile error):
val template = "User {name} has {points} points"
val msg = template.with({"name": "Alice"})  # COMPILE ERROR: missing key "points"
```

**Benefits:**
- Catch typos at compile time
- Prevent missing keys
- IDE autocomplete for required keys
- Refactoring safety

---

## Current Status

### Simple's Strings

Simple has string interpolation but no const key tracking:

```simple
# String interpolation works:
print "Hello {name}!"

# But template validation doesn't:
val template = "Hello {name}"
val msg = template.with({"nme": "Alice"})  # Runtime error (typo not caught)
```

### Missing Features

1. ✅ **Already have:** String interpolation
2. ❌ **Need:** Key extraction from templates
3. ❌ **Need:** ConstKeySet type
4. ❌ **Need:** Key validation at `.with()` calls
5. ❌ **Need:** Error messages for missing/extra keys

---

## Phase Breakdown

### Phase 8A: Key Extraction (2 hours)

**Goal:** Extract keys from string literals at compile time

**Data Structures:**

```simple
# Const key set (compile-time known keys)
class ConstKeySet:
    keys: [Symbol]  # List of required keys

    static fn from_template(template: text) -> ConstKeySet
    fn has_key(key: Symbol) -> bool
    fn missing_keys(provided: [Symbol]) -> [Symbol]
    fn extra_keys(provided: [Symbol]) -> [Symbol]

# Key extractor
class KeyExtractor:
    """Extract keys from string template"""

    fn extract_keys(template: text) -> [Symbol]:
        """
        Extract keys from template string

        Examples:
            "Hello {name}" → ["name"]
            "{x} + {y} = {sum}" → ["x", "y", "sum"]
            "No keys here" → []
        """
        var keys = []
        var in_brace = false
        var current_key = ""

        for char in template:
            if char == '{':
                in_brace = true
                current_key = ""
            elif char == '}':
                if in_brace and current_key.len() > 0:
                    keys.push(current_key)
                in_brace = false
            elif in_brace:
                current_key = current_key + char

        keys
```

**Examples:**

```simple
# Example 1: Simple template
val template = "Hello {name}"
val keys = KeyExtractor.extract_keys(template)
# keys = ["name"]

# Example 2: Multiple keys
val template = "User {name} has {points} points"
val keys = KeyExtractor.extract_keys(template)
# keys = ["name", "points"]

# Example 3: Duplicate keys
val template = "{x} + {x} = {sum}"
val keys = KeyExtractor.extract_keys(template)
# keys = ["x", "x", "sum"]  # Duplicates preserved
```

**Tests:**
- Extract single key
- Extract multiple keys
- Extract no keys (plain string)
- Extract duplicate keys
- Handle nested braces
- Handle malformed templates

---

### Phase 8B: ConstKeySet Type (2 hours)

**Goal:** Type system support for const key sets

**Type Extension:**

```simple
# Extended HirType
enum HirType:
    # ... existing variants ...
    ConstKeySet(keys: [Symbol])      # NEW: compile-time known keys
    DependentKeys(source: Symbol)    # NEW: keys from variable

impl HirType:
    fn is_const_key_set() -> bool:
        match self:
            case ConstKeySet(_): true
            case _: false

    fn get_keys() -> [Symbol]:
        """Get keys if ConstKeySet, empty otherwise"""
        match self:
            case ConstKeySet(keys): keys
            case _: []

# Type inference for templates
class TemplateTypeInference:
    """Infer ConstKeySet type for string templates"""

    fn infer_template(template: text) -> HirType:
        """
        Infer type of template string

        Returns: ConstKeySet with extracted keys
        """
        val keys = KeyExtractor.extract_keys(template)
        HirType.ConstKeySet(keys: keys)
```

**Examples:**

```simple
# Example 1: Template type
val template = "Hello {name}, you are {age} years old"
# Type: ConstKeySet(["name", "age"])

# Example 2: Plain string (no keys)
val plain = "Hello world"
# Type: String (not ConstKeySet)

# Example 3: Dependent keys (runtime)
fn make_template(key: text) -> text:
    "Value: {key}"  # Key not known at compile time
# Type: DependentKeys("key")
```

**Tests:**
- Infer ConstKeySet for template
- Infer String for plain text
- ConstKeySet with no keys
- ConstKeySet with multiple keys
- Type equality checking

---

### Phase 8C: Key Validation (2 hours)

**Goal:** Validate `.with()` calls against ConstKeySet

**Validation Algorithm:**

```simple
class ConstKeyValidator:
    """Validates keys in .with() calls"""

    fn validate_with_call(
        template_ty: HirType,
        provided_keys: [Symbol]
    ) -> Result<(), KeyError>:
        """
        Validate .with() call

        Checks:
        1. Template type is ConstKeySet
        2. All required keys are provided
        3. No extra keys are provided
        """
        # 1. Check template type
        if not template_ty.is_const_key_set():
            return Error("Not a template with const keys")

        val required_keys = template_ty.get_keys()

        # 2. Check for missing keys
        val missing = self.find_missing_keys(required_keys, provided_keys)
        if missing.len() > 0:
            return Error("Missing keys: {missing}")

        # 3. Check for extra keys
        val extra = self.find_extra_keys(required_keys, provided_keys)
        if extra.len() > 0:
            return Error("Unknown keys: {extra}")

        Ok(())

    fn find_missing_keys(required: [Symbol], provided: [Symbol]) -> [Symbol]:
        """Find keys in required but not in provided"""
        var missing = []
        for key in required:
            if key not in provided:
                missing.push(key)
        missing

    fn find_extra_keys(required: [Symbol], provided: [Symbol]) -> [Symbol]:
        """Find keys in provided but not in required"""
        var extra = []
        for key in provided:
            if key not in required:
                extra.push(key)
        extra
```

**Examples:**

```simple
# Example 1: Valid call
val template = "Hello {name}"  # ConstKeySet(["name"])
val msg = template.with({"name": "Alice"})  # OK

# Example 2: Missing key
val template = "User {name} has {points} points"
val msg = template.with({"name": "Bob"})
# ERROR: Missing keys: ["points"]

# Example 3: Extra key
val template = "Hello {name}"
val msg = template.with({"name": "Alice", "age": 30})
# ERROR: Unknown keys: ["age"]

# Example 4: Typo
val template = "Hello {name}"
val msg = template.with({"nme": "Alice"})
# ERROR: Missing keys: ["name"], Unknown keys: ["nme"]
```

**Tests:**
- Valid with call (all keys provided)
- Missing key error
- Extra key error
- Multiple missing keys
- Multiple extra keys
- Typo detection (missing + extra)

---

## Examples

### Example 1: Basic Template

```simple
val template = "Hello {name}, welcome to {place}!"
val msg = template.with({
    "name": "Alice",
    "place": "Simple Land"
})
# OK: all keys provided

val bad = template.with({"name": "Bob"})
# ERROR: Missing key "place"
```

### Example 2: User Profile

```simple
val profile_template = "User {username} (ID: {user_id})\nEmail: {email}\nJoined: {join_date}"

val profile = profile_template.with({
    "username": "alice123",
    "user_id": 42,
    "email": "alice@example.com",
    "join_date": "2024-01-01"
})
# OK: all keys provided

val incomplete = profile_template.with({
    "username": "bob456",
    "user_id": 99
})
# ERROR: Missing keys: ["email", "join_date"]
```

### Example 3: SQL Query Template

```simple
val query_template = "SELECT * FROM {table} WHERE {column} = {value}"

val query = query_template.with({
    "table": "users",
    "column": "age",
    "value": 25
})
# OK

val typo = query_template.with({
    "table": "users",
    "colmn": "age",  # Typo: colmn instead of column
    "value": 25
})
# ERROR: Missing keys: ["column"], Unknown keys: ["colmn"]
```

### Example 4: Localization

```simple
val en_template = "You have {count} new messages"
val fr_template = "Vous avez {count} nouveaux messages"

# Both templates have same key structure
fn format_message(template: ConstKeySet<["count"]>, count: i32) -> text:
    template.with({"count": count})

val en_msg = format_message(en_template, 5)
val fr_msg = format_message(fr_template, 5)
```

### Example 5: Error Messages

```simple
val error_template = "Error at line {line}, column {col}: {message}"

fn report_error(line: i32, col: i32, msg: text):
    val error = error_template.with({
        "line": line,
        "col": col,
        "message": msg
    })
    println(error)

report_error(42, 10, "Unexpected token")
# Output: "Error at line 42, column 10: Unexpected token"
```

---

## Testing Strategy

### Test Categories

1. **Key Extraction (Phase 8A):**
   - Extract single key
   - Extract multiple keys
   - Extract no keys
   - Extract duplicate keys
   - Handle nested braces
   - Malformed templates

2. **ConstKeySet Type (Phase 8B):**
   - Infer ConstKeySet type
   - Type equality
   - Get keys from type
   - Type checking predicates

3. **Key Validation (Phase 8C):**
   - Valid with call
   - Missing key error
   - Extra key error
   - Multiple errors
   - Typo detection

### Test Count: ~18 tests

---

## Performance Characteristics

### Time Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Key extraction | O(n) | n = template length |
| Find missing keys | O(r × p) | r = required, p = provided |
| Find extra keys | O(p × r) | p = provided, r = required |
| Validation | O(r × p) | Full validation |

### Space Complexity

| Structure | Complexity | Notes |
|-----------|-----------|-------|
| ConstKeySet | O(k) | k = number of keys |
| Key list | O(k) | Extracted keys |

---

## Integration with Existing Systems

### 1. Type Checker Integration

```simple
# In type_infer.spl
me infer_expr(expr: Expr) -> Result<HirType, TypeError>:
    match expr:
        case StrLit(value):
            # Check if template (has keys)
            val keys = KeyExtractor.extract_keys(value)
            if keys.len() > 0:
                return Ok(HirType.ConstKeySet(keys: keys))
            else:
                return Ok(HirType.Str)

        case MethodCall(receiver, "with", args):
            # Validate .with() call
            val receiver_ty = self.infer_expr(receiver)?

            if receiver_ty.is_const_key_set():
                # Extract keys from dict argument
                val provided_keys = self.extract_dict_keys(args[0])?

                # Validate
                self.const_key_validator.validate_with_call(receiver_ty, provided_keys)?

                return Ok(HirType.Str)
```

### 2. String Interpolation

Const keys work with existing string interpolation:

```simple
# String interpolation (immediate)
val name = "Alice"
val msg = "Hello {name}"  # Interpolated immediately

# Template (deferred)
val template = "Hello {name}"  # ConstKeySet(["name"])
val msg = template.with({"name": "Alice"})  # Interpolated later
```

### 3. Format Macro Integration (Phase 7)

Const keys can be used in macros:

```simple
@macro format_log(level: text, template: ConstKeySet<[...]>, args: Dict):
    println("[{level}] " + template.with(args))
```

---

## Limitations

### 1. No Runtime Key Checking

Keys must be compile-time constants:

```simple
# Supported: Compile-time keys
val template = "Hello {name}"  # ConstKeySet

# Not supported: Runtime keys
fn make_template(key: text) -> text:
    "Value: {key}"  # DependentKeys (runtime)
```

**Future:** Add runtime key validation with DependentKeys type.

### 2. No Nested Templates

Templates don't support nested templates:

```simple
# Not supported:
val outer = "Outer: {inner}"
val inner = "Inner: {value}"
val msg = outer.with({"inner": inner.with({"value": 42})})
```

**Future:** Add nested template support.

### 3. No Key Expressions

Keys must be simple identifiers:

```simple
# Supported:
"{name}"

# Not supported:
"{user.name}"  # Dotted path
"{names[0]}"   # Array indexing
```

**Future:** Add expression support in keys.

---

## Next Steps

After Phase 8:
1. **Phase 9:** SIMD Complete (4h)
2. **Phase 1:** Bidirectional Type Checking (12h) - deferred

---

## File Structure

```
src/compiler/
  const_keys_phase8a.spl         # Key extraction (2h)
  const_keys_phase8b.spl         # ConstKeySet type (2h)
  const_keys_phase8c.spl         # Key validation (2h)

doc/plan/
  const_keys_implementation_plan.md  # This file

doc/report/
  const_keys_complete_2026-02-03.md  # To be created
```

---

## Success Criteria

✅ All 3 phases implemented
✅ 18+ tests passing
✅ Key extraction from templates
✅ ConstKeySet type in type system
✅ Validation of .with() calls
✅ Error messages for missing/extra keys
✅ Integration with type checker

---

**Status:** Ready to implement
**Next:** Phase 8A - Key Extraction (2 hours)
