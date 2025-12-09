# Feature: Enums (#11)

**Core Type Feature**
- **Importance**: 5/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable enum definition and variant usage:
```
enum Color:
    Red
    Green
    Blue

let c = Color::Red
main = if c is Color::Red: 1 else: 0
```

## Implementation Plan

### Parser
- Enum definition already parsed
- Need enum variant access syntax: `EnumName::Variant`

### Compiler
- Store enum definitions
- Handle `Path` expression for `EnumName::Variant`
- Support `is` comparison for enum variants

## Test Case

```rust
#[test]
fn runner_handles_enums() {
    let src = r#"
enum Color:
    Red
    Green
    Blue

let c = Color::Red
main = if c is Color::Red: 1 else: 0
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 1);
}
```

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Add `Expr::Path` to AST for `EnumName::Variant` syntax
- [x] Parse `Name::Name` as Path expression
- [x] Add `Value::Enum` type to compiler
- [x] Handle `Node::Enum` to store enum definitions
- [x] Handle `Expr::Path` to create enum values
- [x] Update `BinOp::Is` to compare enum values properly
- [x] Verify all tests pass (TDD: Green) - 92 tests pass
