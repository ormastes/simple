# File Splitting Status

## Completed
- ✅ Fixed syntax error in `src/compiler/src/codegen/llvm_tests/mir_compilation.rs`
- ✅ Fixed backend selection logic in `src/compiler/src/codegen/backend_trait.rs`
- ✅ All tests passing (631+ tests)

## Files Requiring Splitting (>1000 lines)

### 1. src/compiler/src/codegen/llvm.rs (1071 lines)
**Priority:** High  
**Risk:** Medium (feature-gated, modular)  
**Duplication:** Multiple 51-line blocks in compile_function, compile_binop, test helpers

**Proposed Structure:**
```
src/compiler/src/codegen/llvm/
├── mod.rs           - Re-exports and module organization
├── backend.rs       - LlvmBackend struct, new(), basic operations
├── types.rs         - Type mapping, LlvmType enum
├── module.rs        - Module and function creation
├── codegen.rs       - compile_function, compile_binop/unary/terminator
├── emit.rs          - Object file emission
└── test_helpers.rs  - Test helper functions
```

### 2. src/parser/src/ast.rs (1045 lines)
**Priority:** High  
**Risk:** Low (pure data definitions, no logic)  
**Duplication:** Minimal (mostly struct/enum definitions)

**Proposed Structure:**
```
src/parser/src/ast/
├── mod.rs         - Node enum, re-exports
├── common.rs      - Visibility, Mutability, RangeBound, SelfMode, MoveMode
├── docs.rs        - DocComment, Decorator, Attribute  
├── definitions.rs - FunctionDef, StructDef, ClassDef, TraitDef, ImplBlock
├── enums.rs       - EnumDef, EnumVariant, UnitDef, UnitVariant, UnitFamilyDef
├── macros.rs      - MacroDef, MacroPattern, MacroInvocation, MacroArg
├── statements.rs  - LetStmt, IfStmt, MatchStmt, ForStmt, WhileStmt, etc
├── contracts.rs   - ContractBlock, ContractClause, InvariantBlock
├── modules.rs     - Import, Export, Use statements, ModulePath
└── expressions.rs - Expr enum and related types
```

### 3. src/compiler/src/hir/lower.rs (1023 lines)
**Priority:** Medium  
**Risk:** High (complex logic, many dependencies)  
**Duplication:** Multiple duplicates in lower_expr, lower_node, lower_module

**Proposed Structure:**
```
src/compiler/src/hir/lower/
├── mod.rs         - Lowerer struct, re-exports
├── module.rs      - Module lowering
├── node.rs        - Node lowering  
├── expr.rs        - Expression lowering
├── types.rs       - Type resolution
└── inference.rs   - Type inference helpers
```

### 4. src/loader/src/settlement/container.rs (1005 lines)
**Priority:** Low  
**Risk:** High (integration code, complex state management)  
**Duplication:** Duplicates in add_module_with_linking, remove_module, replace_module

**Proposed Structure:**
```
src/loader/src/settlement/container/
├── mod.rs           - SettlementContainer struct
├── module_ops.rs    - add_module, remove_module, replace_module
├── linking.rs       - Symbol resolution and linking logic
├── compaction.rs    - Memory compaction and cleanup
└── validation.rs    - Container validation logic
```

## Implementation Plan

### Phase 1: Low-Risk Splits (ast.rs)
1. Create ast/ directory structure
2. Move pure data definitions (no behavior changes)
3. Run tests after each file
4. Update imports across codebase

### Phase 2: Medium-Risk Splits (llvm.rs)
1. Create llvm/ directory structure  
2. Split feature-gated sections (easier to test in isolation)
3. Verify test helpers work correctly
4. Run full test suite

### Phase 3: High-Risk Splits (lower.rs, container.rs)
1. Analyze dependencies carefully
2. Extract helper functions first to reduce duplication
3. Split into modules only after helpers are stable
4. Run integration tests between each step

## Testing Strategy

After each split:
1. Run unit tests: `cargo test -p <crate> --lib`
2. Run integration tests: `cargo test`
3. Check duplication: `make duplication-simple`
4. Verify line counts: No file should exceed 1000 lines

## Success Criteria

- ✅ All tests pass
- ✅ No file exceeds 1000 lines
- ✅ Duplication reduced (especially 51-line blocks)
- ✅ Code organization improved (better separation of concerns)
- ✅ No breaking changes to public API
