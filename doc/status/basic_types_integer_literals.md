# Feature: Basic Types - Integer Literals

**Feature #1 from feature.md**
- **Importance**: 5/5
- **Difficulty**: 1/5
- **Status**: COMPLETED

## Goal

Make the compiler actually compile integer literals so that `main = 42` returns 42 (not always 0).

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Test: `runner.run_source("main = 42")` should return 42
- Test added in `src/driver/tests/runner_tests.rs`
- Test initially failed (returned 0 instead of 42)

### Phase 2: Implementation (Green) - DONE
- Modified `src/compiler/src/lib.rs`:
  - Added `extract_main_value()` to parse AST and find `main = <integer>`
  - Modified `write_smf_with_return_value()` to generate x86-64 `mov eax, imm32; ret`
  - Changed from always `xor eax, eax; ret` (return 0) to dynamic value

### Phase 3: Verify (All Tests Pass) - DONE
- All 64 workspace tests pass
- System test `runner_returns_integer_literal_value` passes

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added AST parsing, integer extraction, x86-64 codegen |
| `src/driver/tests/runner_tests.rs` | Added system test for integer return values |

## Progress

- [x] System test written
- [x] Compiler modified to extract main value from AST
- [x] x86-64 codegen generates `mov eax, <value>; ret`
- [x] All tests passing (64/64)

## Implementation Details

```rust
// Extract integer from `main = <int>` assignment
fn extract_main_value(items: &[Node]) -> Result<i32, CompileError>

// Generate x86-64: mov eax, imm32; ret
let code_bytes = {
    let mut code = Vec::with_capacity(6);
    code.push(0xB8u8); // mov eax, imm32
    code.extend_from_slice(&return_value.to_le_bytes());
    code.push(0xC3); // ret
    code
};
```

## Next Features

Now that integer literals work, the next logical steps are:
- Variables (`let x = 42`) - Feature #2
- Arithmetic operators (`1 + 2`) - Feature #4
- Other basic types (bool, float) - Feature #1 continuation
