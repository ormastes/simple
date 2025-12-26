# Feature: Dictionary Types (#42)

**Core Type Feature**
- **Importance**: 4/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable dictionary literal creation and key-based access:
```
let d = {"name": "Alice", "age": 30}
main = d["age"]  # returns 30
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_dictionary_types`
- Tests: string keys, integer keys, arithmetic with values, variable key lookup, empty dict

### Phase 2: Implementation (Green) - DONE
- Added `Value::Str(String)` variant for string values
- Added `Expr::String` handling in `evaluate_expr()`
- Added `to_key_string()` method for clean key representation
- Updated `Expr::Dict` to use `to_key_string()` for keys
- Added `__dict__` case in `Expr::Index` for key-based lookup

### Phase 3: Verify - DONE
- All 21 driver tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added Value::Str, Expr::String, to_key_string(), updated Dict and Index |
| `src/driver/tests/runner_tests.rs` | Added dictionary tests |

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Add Value::Str variant
- [x] Add Expr::String handling
- [x] Add to_key_string() method
- [x] Update Expr::Dict for clean key format
- [x] Update Expr::Index for dict lookup
- [x] Verify all tests pass (TDD: Green)

## Implementation Details

### Value::Str Added
```rust
enum Value {
    Int(i64),
    Bool(bool),
    Str(String),  // NEW
    Object { class: String, fields: HashMap<String, Value> },
    Enum { enum_name: String, variant: String, payload: Option<Box<Value>> },
    Nil,
}
```

### to_key_string() Method
```rust
fn to_key_string(&self) -> String {
    match self {
        Value::Int(i) => i.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => s.clone(),
        Value::Nil => "nil".to_string(),
        other => format!("{other:?}"),
    }
}
```

### Dict Index Lookup
```rust
if class == "__dict__" {
    let key = idx_val.to_key_string();
    fields.get(&key).cloned()
        .ok_or_else(|| CompileError::Semantic(format!("dict key not found: {key}")))
}
```

## What Now Works

```
# String keys
let d = {"a": 10, "b": 20, "c": 30}
main = d["a"]           # returns 10

# Integer keys
let d = {1: 100, 2: 200, 3: 300}
main = d[2]             # returns 200

# Value arithmetic
let d = {"x": 5, "y": 7}
main = d["x"] + d["y"]  # returns 12

# Variable key lookup
let d = {"first": 1, "second": 2}
let key = "second"
main = d[key]           # returns 2

# Empty dict
let d = {}
main = 42               # works
```

## Notes

- Dictionaries are stored as `Value::Object { class: "__dict__", fields: HashMap }`
- Keys are converted to strings using `to_key_string()` for consistent lookup
- Both string and integer keys work via the unified key string format
- Added `Value::Str` enables proper string literal handling throughout the compiler
