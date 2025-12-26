# Feature: Option Type (#38)

**Core Type Feature**
- **Importance**: 4/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## Goal

Support enum variants with payloads to enable Option-like types:
```
enum Option:
    Some(i64)
    None

let x = Option::Some(42)
match x:
    Option::Some(v) =>
        result = v
    Option::None =>
        result = 0
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_option_type`
- Tests: Some variant construction, None variant, pattern matching with payload extraction

### Phase 2: Implementation (Green) - DONE
- Updated `Value::Enum` to include `payload: Option<Box<Value>>`
- Added `Expr::Path` handling in `Expr::Call` for enum variant constructors
- Updated `Pattern::Enum` matching to extract payload values

### Phase 3: Verify - DONE
- All 19 driver tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Updated Value::Enum, added enum constructor call, updated pattern matching |
| `src/driver/tests/runner_tests.rs` | Added Option type tests |

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Update Value::Enum to support payload
- [x] Add enum variant constructor in Expr::Call
- [x] Update Pattern::Enum to extract payload
- [x] Verify all tests pass (TDD: Green)

## Implementation Details

### Value::Enum Updated
```rust
Enum { enum_name: String, variant: String, payload: Option<Box<Value>> },
```

### Enum Constructor in Expr::Call
```rust
if let Expr::Path(segments) = callee.as_ref() {
    if segments.len() == 2 {
        let enum_name = &segments[0];
        let variant = &segments[1];
        if let Some(variants) = enums.get(enum_name) {
            if variants.contains(variant) {
                let payload = if !args.is_empty() {
                    Some(Box::new(evaluate_expr(&args[0].value, ...)?))
                } else {
                    None
                };
                return Ok(Value::Enum { enum_name, variant, payload });
            }
        }
    }
}
```

### Pattern Matching with Payload
```rust
Pattern::Enum { name, variant, payload } => {
    if let Value::Enum { enum_name: ve, variant: vv, payload: value_payload } = value {
        if name == ve && variant == vv {
            // Match and bind payload if present
            if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                if patterns.len() == 1 {
                    pattern_matches(&patterns[0], vp.as_ref(), bindings, enums)?;
                }
            }
        }
    }
}
```

## What Now Works

```
enum Option:
    Some(i64)
    None

# Construction
let x = Option::Some(42)
let y = Option::None

# Pattern matching with extraction
match x:
    Option::Some(v) =>
        result = v      # v binds to 42
    Option::None =>
        result = 0

# In functions
fn get_value(opt):
    match opt:
        Option::Some(v) =>
            return v
        Option::None =>
            return 0
```

## Notes

- This implementation supports user-defined Option-like enums
- The `T?` syntax sugar (mentioned in feature spec) would require additional parser work
- Currently supports single payload values; multiple payloads would need tuple support
- Works with pattern matching to extract payload values into bindings
