# Long Rust Source Files

This document tracks Rust source files over 1000 lines and explains why they remain unsplit.

**Last updated:** 2025-12-22

## Summary

**19 Rust files over 1000 lines** - Not split due to code cohesion requirements.

## Why Not Split?

Unlike markdown documentation, splitting Rust source files can:
- Break logical cohesion of related code
- Make navigation harder (jumping between related functions)
- Complicate module structure
- Reduce compiler optimization opportunities
- Create artificial boundaries in tightly coupled code

## Long Files (>1000 lines)

### Compiler - MIR Layer
- **`src/compiler/src/mir/lower.rs`** (2486 lines)
  - Single `MirLowerer` struct with large impl block
  - HIR→MIR transformation logic tightly coupled
  - **Recommendation:** Keep together

### Compiler - LLVM Codegen
- **`src/compiler/src/codegen/llvm/mod.rs`** (1843 lines)
  - LLVM backend main implementation
  - Complex state management for code generation
  - **Recommendation:** Keep together

### Compiler - Interpreter
- **`src/compiler/src/interpreter.rs`** (1728 lines)
  - Tree-walking interpreter main loop
  - Already partially split (interpreter_expr.rs, interpreter_call.rs, interpreter_method.rs)
  - **Recommendation:** Already well-factored

- **`src/compiler/src/interpreter_method.rs`** (1455 lines)
  - Built-in method implementations
  - Collection of related method handlers
  - **Recommendation:** Keep together

- **`src/compiler/src/interpreter_call.rs`** (1398 lines)
  - Function call handling
  - **Recommendation:** Keep together

- **`src/compiler/src/interpreter_expr.rs`** (1310 lines)
  - Expression evaluation
  - **Recommendation:** Keep together

### Compiler - HIR Layer
- **`src/compiler/src/hir/lower/expr_lowering.rs`** (1545 lines)
  - Expression lowering from parser AST to HIR
  - Single focused responsibility
  - **Recommendation:** Keep together

- **`src/compiler/src/hir/types.rs`** (1262 lines)
  - HIR type definitions and operations
  - Cohesive type system implementation
  - **Recommendation:** Keep together

### Compiler - Other
- **`src/compiler/src/codegen/instr.rs`** (1414 lines)
  - Instruction encoding/generation
  - **Recommendation:** Keep together

- **`src/compiler/src/module_resolver.rs`** (1057 lines)
  - Module resolution logic
  - **Recommendation:** Keep together

- **`src/compiler/src/coverage.rs`** (1155 lines)
  - Coverage instrumentation
  - **Recommendation:** Keep together

### Parser
- **`src/parser/src/ast/nodes.rs`** (1497 lines)
  - AST node definitions (structs/enums)
  - Single cohesive type collection
  - **Recommendation:** Keep together (splitting would scatter type definitions)

### Driver - Tests
- **`src/driver/tests/interpreter_types.rs`** (1213 lines)
  - Integration tests
  - **Recommendation:** Could split by test categories if needed

### Parser - Tests  
- **`src/parser/src/parser_tests.rs`** (1128 lines)
  - Unit tests (64 tests)
  - **Recommendation:** Could split into parser_tests_{basic,advanced}.rs

- **`src/parser/tests/parser_tests.rs`** (1026 lines)
  - Integration tests (102 tests)
  - **Recommendation:** Could split by feature area

### Compiler - Tests
- **`src/compiler/src/hir/lower/lower_tests.rs`** (1520 lines)
  - HIR lowering tests (83 tests)
  - **Recommendation:** Could split into lower_tests_{expr,stmt,types}.rs

### MIR
- **`src/compiler/src/mir/instructions.rs`** (1456 lines)
  - MIR instruction definitions
  - **Recommendation:** Keep together

### UI
- **`src/ui/src/parser/mod.rs`** (1026 lines)
  - UI parser
  - **Recommendation:** Keep together

### Utilities
- **`src/util/simple_mock_helper/src/coverage_extended.rs`** (1036 lines)
  - Mock helper coverage
  - **Recommendation:** Keep together

## Best Practices

For Rust code organization:

1. **Prefer cohesion over arbitrary line limits**
   - Keep tightly related code together
   - Split when there are clear module boundaries

2. **Split when it makes sense:**
   - Different feature areas (e.g., `interpreter_expr.rs`, `interpreter_call.rs`)
   - Test suites by feature category
   - Clear sub-modules with minimal coupling

3. **Don't split:**
   - Single large impl blocks
   - Tightly coupled functions
   - Type definition collections
   - State machines with shared state

## Future Refactoring

If files grow beyond 2000 lines, consider:
- Extracting clear sub-modules
- Moving helper functions to separate modules
- Grouping related functionality
- But only if natural boundaries exist

---

## Split Attempt (2025-12-22)

**Attempted:** Splitting test files at ~500 line boundaries  
**Result:** Failed - splits occurred mid-function, breaking compilation  
**Lesson:** Rust files cannot be blindly split at arbitrary line counts

### Why Splitting Failed:

1. **Context sensitivity**: Test helper functions at top are used by tests throughout
2. **Mid-function splits**: Arbitrary line cuts can break functions
3. **Import dependencies**: Each part needs correct imports from parent module
4. **State sharing**: Tests may share setup code and fixtures

### Correct Approach for Test Files:

If test files must be split:
1. **Manual grouping** by feature area (e.g., `expr_tests.rs`, `stmt_tests.rs`)
2. **Extract helpers** into a shared test module
3. **Split at logical boundaries** not line counts
4. **Ensure each file** is independently compilable

**Conclusion:** Rust source files >1000 lines are acceptable and preferred over
artificially split files that harm code organization.
