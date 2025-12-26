# Feature: Structs (#9)

**Core Type Feature**
- **Importance**: 5/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable struct definition, instantiation, and field access:
```
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y  # returns 30
```

## Implementation Plan

### Parser Changes
- Struct definition already parsed (`struct Name:\n    field: Type`)
- Need to add struct initialization expression parsing: `Name { field: value, ... }`
- Currently `Identifier { ... }` just returns Identifier, then `{...}` is parsed as Dict

### Compiler Changes
- Struct definitions: store struct metadata
- Struct initialization: create Value::Struct with field values
- Field access: look up field in struct value

## Files to Modify

| File | Change |
|------|--------|
| `src/parser/src/parser.rs` | Parse `Name { field: value }` as StructInit |
| `src/compiler/src/lib.rs` | Handle struct definitions and instantiation |
| `src/driver/tests/runner_tests.rs` | Add test for struct feature |

## Test Case

```rust
#[test]
fn runner_handles_structs() {
    let src = r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 30);
}
```

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Implement parser changes for struct init
- [x] Compiler already had struct support
- [x] Verify all tests pass (TDD: Green) - 91 tests pass
