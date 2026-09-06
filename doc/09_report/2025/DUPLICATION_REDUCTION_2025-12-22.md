# Code Duplication Reduction Plan

**Date:** 2025-12-22  
**Current Status:** 4.49% duplication (5,576 lines, 379 clones)  
**Target:** Below 2.5% threshold  
**Required Reduction:** ~1.99% (about 2,500 lines)

## Current State

```
┌────────┬────────────────┬─────────────┬──────────────┬──────────────┬──────────────────┬───────────────────┐
│ Format │ Files analyzed │ Total lines │ Total tokens │ Clones found │ Duplicated lines │ Duplicated tokens │
├────────┼────────────────┼─────────────┼──────────────┼──────────────┼──────────────────┼───────────────────┤
│ rust   │ 414            │ 124259      │ 1036943      │ 379          │ 5576 (4.49%)     │ 52764 (5.09%)     │
└────────┴────────────────┴─────────────┴──────────────┴──────────────┴──────────────────┴───────────────────┘
```

## Top Duplicated Files

| File | Clones | Category |
|------|--------|----------|
| net_udp.rs | 19 | Runtime networking |
| net_tcp.rs | 13 | Runtime networking |
| interpreter_native_net.rs | 13 | Interpreter bindings |
| interpreter_helpers_option_result.rs | 11 | Interpreter helpers |
| llvm_tests/mir_compilation.rs | 11 | Test code |
| interpreter_helpers.rs | 10 | Interpreter helpers |
| llvm/gpu.rs | 7 | LLVM GPU backend |

## Refactoring Strategy

### Phase 1: Network FFI Helpers (Target: -800 lines)

**Files:** `net_udp.rs`, `net_tcp.rs`, `interpreter_native_net.rs`

**Pattern:** Repeated error handling and socket registry access

**Solution:**
- Extract `get_socket_from_registry<T>()` helper
- Create `socket_registry_access!()` macro
- Extract `parse_and_validate_addr()` helper
- Create `ffi_error_wrapper!()` macro for consistent error returns

### Phase 2: Interpreter Helpers (Target: -400 lines)

**Files:** `interpreter_helpers_option_result.rs`, `interpreter_helpers.rs`

**Pattern:** Similar Option/Result unwrapping patterns

**Solution:**
- Extract `unwrap_option_or_error()` helper
- Create `result_handler!()` macro
- Consolidate error conversion functions

### Phase 3: Test Helpers (Target: -600 lines)

**Files:** `llvm_tests/*.rs`

**Pattern:** Repeated test setup and assertion code

**Solution:**
- Extract `compile_and_assert()` helper
- Create `test_mir_instruction!()` macro
- Consolidate test fixtures in `llvm_tests/helpers.rs`

### Phase 4: GPU Code (Target: -300 lines)

**Files:** `llvm/gpu.rs`

**Pattern:** Repeated LLVM type conversion and function creation

**Solution:**
- Extract `create_gpu_function()` helper
- Create `gpu_type_conversion!()` macro
- Consolidate CUDA/PTX function builders

### Phase 5: Minor Duplications (Target: -400 lines)

**Files:** Various smaller duplications

**Solution:**
- Extract common patterns into utility modules
- Create builder patterns where appropriate
- Use macros for repetitive code generation

## Expected Outcome

| Phase | Lines Reduced | New Duplication % |
|-------|---------------|-------------------|
| Current | - | 4.49% |
| Phase 1 | -800 | 3.84% |
| Phase 2 | -400 | 3.52% |
| Phase 3 | -600 | 3.04% |
| Phase 4 | -300 | 2.80% |
| Phase 5 | -400 | 2.48% |
| **Target** | **-2500** | **~2.4% ✓** |

## Implementation Notes

- Each phase should maintain all tests passing
- Focus on high-impact files first (most clones)
- Use macros sparingly - prefer helper functions
- Document extracted helpers clearly
- Run `cargo test` after each phase

## Success Criteria

✅ Duplication below 2.5% threshold  
✅ All tests passing  
✅ No regression in build time  
✅ Code remains readable and maintainable

