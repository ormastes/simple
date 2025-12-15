# Code Duplication Report

## Summary

Analyzed codebase for duplicate code blocks using jscpd (min 5 lines, min 50 tokens).

## Files Requiring Attention

### Large Files (>1000 lines)
1. `src/compiler/src/codegen/llvm.rs` - 1071 lines
   - Multiple 51-line duplicates in compile_function, compile_binop, test helpers
   - Recommendation: Split into modules (backend, types, codegen, emit, test_helpers)

2. `src/parser/src/ast.rs` - 1045 lines  
   - Pure data definitions (structs/enums)
   - Recommendation: Split by concept (common, definitions, enums, macros, statements, contracts, modules, expressions)

3. `src/compiler/src/hir/lower.rs` - 1023 lines
   - Multiple duplicates in lower_expr, lower_node, lower_module
   - Recommendation: Split into modules (module, node, expr, types, inference)

4. `src/loader/src/settlement/container.rs` - 1005 lines
   - Duplicates in add_module_with_linking, remove_module, replace_module  
   - Recommendation: Extract helper functions, split concerns

## Immediate Actions

1. Fix syntax error in `src/compiler/src/codegen/llvm_tests/mir_compilation.rs:27` ✅ DONE
2. Run full test suite to establish baseline
3. Create detailed split plans for each file
4. Split files incrementally with tests between each step

## Test Status

- Parser tests: ✅ 105 passed
- Compiler tests: ❌ 1 syntax error (FIXED)

## Next Steps

1. Run full test suite
2. Begin with ast.rs (lowest risk - pure data definitions)
3. Then llvm.rs (modular, feature-gated)
4. Then lower.rs (complex, high risk)
5. Finally container.rs (integration code)
