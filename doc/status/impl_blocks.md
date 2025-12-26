# Feature: Impl Blocks (#16)

**Core Type Feature**
- **Importance**: 4/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable impl block definitions to add methods to structs (and classes):

```
struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

let p = Point { x: 15, y: 25 }
main = p.sum()  # returns 40
```

## Implementation

### Parser Changes
- Parser already supported `impl` blocks via `parse_impl()` in `src/parser/src/parser.rs:729`
- Added support for `self` as a parameter name in function definitions

### Compiler Changes
- Added `ImplMethods` type alias: `HashMap<String, Vec<FunctionDef>>`
- Added handling for `Node::Impl` in `evaluate_module()` to collect impl methods
- Updated `Expr::MethodCall` to check both class methods AND impl block methods
- Fixed `exec_function` to skip `self` parameter when binding arguments (self is bound from context)

## Files Modified

| File | Change |
|------|--------|
| `src/parser/src/parser.rs` | Allow `self` as parameter name in `parse_parameters()` |
| `src/compiler/src/lib.rs` | Add `ImplMethods`, handle `Node::Impl`, update method dispatch |
| `src/driver/tests/interpreter_tests.rs` | Add `interpreter_impl_blocks` and `interpreter_impl_blocks_with_args` tests |

## Test Cases

```rust
#[test]
fn interpreter_impl_blocks() {
    let code = r#"
struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

let p = Point { x: 15, y: 25 }
main = p.sum()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40); // 15 + 25 = 40
}

#[test]
fn interpreter_impl_blocks_with_args() {
    let code = r#"
struct Counter:
    value: i64

impl Counter:
    fn add(self, n):
        return self.value + n

let c = Counter { value: 10 }
main = c.add(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // 10 + 5 = 15
}
```

## Progress

- [x] Parser already supports impl block syntax
- [x] Added `self` parameter support in parser
- [x] Added `ImplMethods` storage in compiler
- [x] Added `Node::Impl` handling to collect methods
- [x] Updated method dispatch to check impl methods
- [x] Fixed self parameter binding in function execution
- [x] Added system tests
- [x] All tests pass (121 tests)
