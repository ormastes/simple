# Large Files Analysis Report

**Date:** 2025-12-31  
**Threshold:** Files over 1000 lines  
**Purpose:** Identify potential refactoring candidates

---

## Summary

**Rust Files:** 7 files over 1000 lines  
**Simple Files:** 4 files over 1000 lines  
**Total:** 11 files requiring attention

---

## Rust Files (Largest to Smallest)

### 1. `src/compiler/src/hir/lower/expr/lowering.rs` - 1,699 lines
**Type:** HIR Expression Lowering  
**Status:** ⚠️ Consider refactoring  
**Recommendation:** Split by expression type categories:
- `lowering_literals.rs` - Integer, Float, String, Bool, Nil
- `lowering_operators.rs` - Binary, Unary, Comparison
- `lowering_calls.rs` - Call, MethodCall, FieldAccess
- `lowering_collections.rs` - Array, Tuple, Dict, comprehensions
- `lowering_control.rs` - If, Match, Lambda
- `lowering_advanced.rs` - Spawn, Await, Yield, patterns

**Impact:** High - complex expression lowering logic

---

### 2. `src/compiler/src/codegen/instr.rs` - 1,425 lines
**Type:** Unified Instruction Compilation  
**Status:** ✅ Already using module includes  
**Comment:** File header mentions "Include split modules for better organization"  
**Recommendation:** Verify split modules are properly organized

**Impact:** Medium - core codegen logic

---

### 3. `src/compiler/src/interpreter_expr.rs` - 1,416 lines
**Type:** Interpreter Expression Evaluation  
**Status:** ⚠️ Consider refactoring  
**Recommendation:** Split by evaluation categories:
- `interpreter_expr_literals.rs` - Primitive values
- `interpreter_expr_operators.rs` - Binary/unary operations
- `interpreter_expr_calls.rs` - Function/method calls
- `interpreter_expr_collections.rs` - Arrays, tuples, dicts
- `interpreter_expr_control.rs` - If, match, lambdas
- `interpreter_expr_async.rs` - Spawn, await, yield
- `interpreter_expr_casting.rs` - Type conversions and units

**Impact:** High - runtime evaluation performance critical

---

### 4. `src/runtime/src/value/gpu_vulkan.rs` - 1,276 lines
**Type:** Vulkan GPU FFI Bridge  
**Status:** ✅ Partially modularized  
**Comment:** Header mentions submodules under `vulkan_ffi/`  
**Recommendation:** 
- Complete migration to submodule structure
- Ensure all FFI functions properly organized by category
- Consider splitting into: device, buffer, pipeline, descriptor, sync

**Impact:** Medium - GPU functionality (not on hot path)

---

### 5. `src/compiler/src/interpreter_macro.rs` - 1,238 lines
**Type:** Macro Expansion  
**Status:** ⚠️ Consider refactoring  
**Recommendation:** Split by macro functionality:
- `interpreter_macro_invocation.rs` - Invocation and dispatch
- `interpreter_macro_expansion.rs` - Token tree expansion
- `interpreter_macro_hygiene.rs` - Symbol tracking and contracts
- `interpreter_macro_builtins.rs` - Built-in macro handlers

**Impact:** Medium - compile-time only

---

### 6. `src/compiler/src/codegen/llvm/functions.rs` - 1,189 lines
**Type:** LLVM Function Compilation  
**Status:** ⚠️ Consider refactoring  
**Comment:** Header mentions "specialized helper methods organized by category"  
**Recommendation:** 
- Split into instruction category modules
- Mirror MIR instruction organization
- Maintain function orchestration in main file

**Impact:** Medium - LLVM backend (alternative to Cranelift)

---

### 7. `src/ui/src/parser/mod.rs` - 1,026 lines
**Type:** SUI Template Parser  
**Status:** ⚠️ Consider refactoring  
**Recommendation:** Split by parsing functionality:
- `parser_core.rs` - Parser struct and utilities
- `parser_tags.rs` - HTML tag parsing
- `parser_expressions.rs` - Expression parsing
- `parser_attributes.rs` - Attribute parsing
- `parser_directives.rs` - SUI directive parsing (@if, @for, etc)

**Impact:** Low - UI template parsing (optional feature)

---

## Simple (.spl) Files

### 1. `simple/std_lib/src/verification/regenerate.spl` - 2,555 lines
**Type:** Code Generation Script  
**Status:** ✅ Acceptable (generated code)  
**Recommendation:** No action needed for code generation scripts

---

### 2. `simple/std_lib/test/features/generate_docs.spl` - 1,247 lines
**Type:** Documentation Generator  
**Status:** ✅ Acceptable (tooling script)  
**Recommendation:** No action needed for build tools

---

### 3. `simple/std_lib/src/host/async_gc_mut/io/fs.spl` - 1,057 lines
**Type:** Filesystem I/O Library  
**Status:** ⚠️ Consider refactoring  
**Recommendation:** Split into logical modules:
- `fs_core.spl` - File/Dir structs and core operations
- `fs_read.spl` - Read operations
- `fs_write.spl` - Write operations
- `fs_metadata.spl` - Metadata and stat operations
- `fs_path.spl` - Path manipulation

---

### 4. `simple/std_lib/src/host/async_nogc_mut/io/fs.spl` - 1,044 lines
**Type:** Filesystem I/O Library (no-GC variant)  
**Status:** ⚠️ Same as above  
**Recommendation:** Apply same splitting strategy

---

## Priority Refactoring Candidates

**High Priority (>1400 lines, hot paths):**
1. `src/compiler/src/hir/lower/expr/lowering.rs` (1,699) - HIR compilation
2. `src/compiler/src/interpreter_expr.rs` (1,416) - Runtime performance

**Medium Priority (1200-1400 lines):**
3. `src/compiler/src/codegen/instr.rs` (1,425) - Check split modules
4. `src/runtime/src/value/gpu_vulkan.rs` (1,276) - Complete modularization
5. `src/compiler/src/interpreter_macro.rs` (1,238) - Compile-time performance

**Low Priority (1000-1200 lines):**
6. `src/compiler/src/codegen/llvm/functions.rs` (1,189) - Alternative backend
7. `src/ui/src/parser/mod.rs` (1,026) - Optional UI feature
8. `simple/std_lib/src/host/*/io/fs.spl` (1,057/1,044) - Standard library

---

## Refactoring Guidelines

1. **Maintain Public API:** Keep existing public functions unchanged
2. **Use Module Hierarchy:** Create subdirectories for related functions
3. **Extract by Category:** Group related functionality together
4. **Preserve Tests:** Ensure all existing tests still pass
5. **Document Splits:** Add module-level documentation explaining organization
6. **Incremental Approach:** Refactor one file at a time, test thoroughly

---

## Next Steps

1. ✅ Document current large files (this report)
2. ⏸️ Prioritize refactoring based on impact and complexity
3. ⏸️ Start with highest priority: `hir/lower/expr/lowering.rs`
4. ⏸️ Create subtask plan for each refactoring
5. ⏸️ Implement, test, and commit incrementally

---

## Notes

- Files under 1000 lines are generally well-sized
- Code generation scripts (regenerate.spl, generate_docs.spl) are exempt
- Some files already use module splitting (instr.rs, gpu_vulkan.rs)
- Focus on runtime hot paths first (HIR lowering, interpreter expressions)
