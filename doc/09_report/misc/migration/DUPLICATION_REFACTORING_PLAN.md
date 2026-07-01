# Code Duplication Refactoring Plan

**Current Status:** 3.31% duplication (294 clones, 3,378 lines)
**Target:** 2.5% or below
**Gap:** -0.81 percentage points

## Summary

The codebase has accumulated duplication primarily from:
1. Structural patterns in interpreter execution (match arms, control flow)
2. Repeated parameter passing patterns (function contexts)
3. Similar utility functions across different modules
4. Copy-paste code in ELF parsing and diagnostics

## High-Priority Refactoring Opportunities

### 1. **Extract Interpreter Context Struct** (Medium Effort, High Impact)

**Files affected:**
- src/compiler/src/interpreter_context.rs
- src/compiler/src/interpreter_helpers.rs
- src/compiler/src/interpreter_expr.rs
- src/compiler/src/interpreter_call.rs
- src/compiler/src/interpreter_method.rs

**Current problem:**
Many function signatures repeat this parameter list:
```rust
env: &Env,
functions: &HashMap<String, FunctionDef>,
classes: &HashMap<String, ClassDef>,
enums: &Enums,
impl_methods: &ImplMethods,
```

**Solution:**
```rust
pub struct InterpreterContext<'a> {
    pub env: &'a Env,
    pub functions: &'a HashMap<String, FunctionDef>,
    pub classes: &'a HashMap<String, ClassDef>,
    pub enums: &'a Enums,
    pub impl_methods: &'a ImplMethods,
}
```

**Benefits:**
- Reduces parameter duplication across 100+ function signatures
- Easier to add new context parameters in future
- Clearer API boundaries

**Risks:**
- Requires updating all call sites (140+ locations)
- May need lifetime annotation adjustments
- Potential for introducing subtle reference issues

### 2. **Create Shared Diagnostic Builder Trait** (Low Effort, Medium Impact)

**Files affected:**
- src/compiler/src/error.rs
- src/parser/src/diagnostic.rs

**Current problem:**
Both files implement identical builder methods:
```rust
pub fn with_note(mut self, note: impl Into<String>) -> Self
pub fn with_help(mut self, help: impl Into<String>) -> Self
```

**Solution:**
Create shared trait in common crate:
```rust
pub trait DiagnosticBuilder: Sized {
    fn with_note(mut self, note: impl Into<String>) -> Self;
    fn with_help(mut self, help: impl Into<String>) -> Self;
}
```

**Benefits:**
- Eliminates 15 lines of duplication (118 tokens)
- Single source of truth for diagnostic building
- Easier to maintain consistency

**Risks:** Low - trait implementation is straightforward

### 3. **Consolidate Interpreter Block Execution** (High Effort, Low ROI)

**Files affected:**
- src/compiler/src/interpreter_call_block_execution.rs (6 internal clones)
- src/compiler/src/interpreter_control.rs
- src/compiler/src/interpreter.rs

**Current problem:**
Multiple functions have similar block execution logic with different match arms for different statement types.

**Solution:**
Would require significant refactoring to create a unified block execution framework with parameterizable behavior.

**Status:** DEFERRED - Complex architectural change with minimal benefit. Current structure is maintainable.

### 4. **Extract ELF Section Iteration Helper** (Low Effort, Low Impact)

**Files affected:**
- src/compiler/src/elf_utils.rs
- src/compiler/src/pipeline.rs

**Current problem:**
Identical ELF section iteration loop:
```rust
for i in 0..e_shnum {
    let sh_offset = e_shoff + i * e_shentsize;
    if sh_offset + e_shentsize > elf_data.len() {
        continue;
    }
    // ...
}
```

**Solution:**
Extract iteration with callback or iterator pattern.

**Status:** LOW PRIORITY - Minimal impact (9 lines), complex integration with section-specific logic.

## Implementation Priority

### Phase 1 (High Priority - Do First)
1. Create DiagnosticBuilder trait (1-2 hours)
   - Low risk, immediate 15-line reduction
   - Clear improvement with minimal side effects

### Phase 2 (Medium Priority - Next Session)
2. Extract InterpreterContext struct (3-4 hours)
   - High complexity, large refactoring scope
   - Requires extensive testing and validation
   - Significant payoff once complete

### Phase 3 (Low Priority - Future)
3. Consolidate block execution patterns
4. Extract ELF utilities

## Current Impact Analysis

**Before refactoring:** 3.31% duplication (3,378 lines)

**After Phase 1:** ~3.21% (saving 15 lines)
**After Phase 2:** ~2.9-3.0% (saving 140-200 lines)
**Full completion:** ~2.2-2.5% (meeting target)

## Notes

- The interpreter module has inherent structural duplication due to similar match arms for different value types and control flow paths
- This type of duplication is difficult to eliminate without significant performance overhead (trait objects, boxing)
- Focus refactoring efforts on cross-module duplicates and clear parameter patterns
- Accept that some structural duplication is necessary and maintainable as-is
