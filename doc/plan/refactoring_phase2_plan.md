# Refactoring Plan: Phase 2 - Stdlib, App, and Test Files

**Date**: 2026-01-30
**Status**: 📋 **Planning**
**Scope**: 28 files over 800 lines (outside compiler scope)

---

## Executive Summary

After completing Phase 1 (compiler refactoring), a comprehensive audit revealed **34 files over 800 lines** across the codebase. Of these:
- **6 compiler files** (Phase 1 ✅ Complete)
- **28 additional files** requiring refactoring:
  - 3 test/spec files
  - 3 app/tooling files
  - 22 standard library files

This plan targets the remaining 28 files with prioritized approach based on size, complexity, and impact.

---

## Priority Levels

### P0: Critical (Files >1400 lines)
**Target**: 3 files, reduce by 40-50% each
- High complexity, maintenance burden
- Clear natural boundaries for splitting

### P1: High Priority (Files 1200-1399 lines)
**Target**: 3 files, reduce by 30-40% each
- Significant size, good split opportunities

### P2: Medium Priority (Files 1000-1199 lines)
**Target**: 4 files, reduce by 25-35% each
- Moderate size, refactor if time permits

### P3: Low Priority (Files 800-999 lines)
**Target**: 18 files, assess case-by-case
- Acceptable size, refactor only if clear benefit

---

## Phase 2.0: Critical Files (P0)

### 1. mocking.spl (1905 lines → 3 files)

**Location**: `simple/std_lib/src/testing/mocking.spl`

**Current Structure**:
- Call tracking (CallRecord, MockFunction) - lines 19-155
- Expectations & Matchers (Expectation, VerificationResult, Matcher) - lines 160-245
- Call Analysis (CallAnalyzer, ReturnValue, SequentialReturns, Spy) - lines 250-370
- Mock Building (MockBuilder, MockRegistry) - lines 375-429
- Policies & Behaviors (MockPolicy, ConditionalReturns, BehaviorSequence) - lines 447-589
- Composition (MockSnapshot, MockComposition) - lines 590-642
- Fluent API (FluentExpectation, WhenBuilder, ProtocolMock, AutoMock) - lines 647-800+

**Proposed Split**:

```
simple/std_lib/src/testing/
├── mocking_core.spl          (~650 lines)
│   - CallRecord, MockFunction
│   - Expectations, Matchers
│   - VerificationResult
│
├── mocking_builders.spl      (~650 lines)
│   - MockBuilder, MockRegistry
│   - Policies, Behaviors
│   - Composition
│
├── mocking_fluent.spl        (~600 lines)
│   - FluentExpectation
│   - WhenBuilder, ProtocolMock
│   - AutoMock
│   - Call Analysis helpers
│
└── mocking.spl               (~20 lines)
    - Re-export module
```

**Benefits**:
- Core mocking separate from advanced features
- Fluent API isolated for easier evolution
- Each file ~600-650 lines (well under target)

---

### 2. regex.spl (1408 lines → 3 files)

**Location**: `src/lib/std/src/core/regex.spl`

**Current Structure**:
- AST Nodes (RegexNode subclasses) - lines 10-104
- NFA (NFAState, NFAFragment, NFA) - lines 106-242
- Parser (RegexParser) - lines 243-548
- Builder (NFABuilder) - lines 549-709
- Matcher (NFAMatcher) - lines 710-836
- Compiled (CompiledRegex) - lines 837-887
- Match (Match class) - lines 888-1007
- Pattern API (Pattern) - lines 1008-1282
- Helper functions - lines 1283-1408

**Proposed Split**:

```
src/lib/std/src/core/
├── regex_parser.spl          (~540 lines)
│   - RegexNode and subclasses (AST)
│   - RegexParser
│
├── regex_engine.spl          (~590 lines)
│   - NFAState, NFAFragment, NFA
│   - NFABuilder
│   - NFAMatcher
│   - CompiledRegex
│
├── regex_api.spl             (~280 lines)
│   - Match class
│   - Pattern class
│   - Helper functions (compile, match, search, etc.)
│   - Builder functions (digit, word, etc.)
│
└── regex.spl                 (~20 lines)
    - Re-export module
```

**Benefits**:
- Parser isolated from engine
- Clean API layer
- Each file under 600 lines

---

### 3. ast_convert.spl (1405 lines → 3 files)

**Location**: `src/app/interpreter/ast_convert.spl`

**Current Structure**:
- AST Type Definitions - lines 16-120
- Helper functions - lines 121-187
- Statement conversions - lines 226-726
- Pattern conversions - lines 740-836
- Expression conversions - lines 837-1352
- Utilities - lines 1385-1405

**Proposed Split**:

```
src/app/interpreter/
├── ast_types.spl             (~200 lines)
│   - Module, Import, Statement
│   - Expr, Pattern, Literal
│   - BinaryOp, UnaryOp enums
│   - Common structs (Param, StructField, etc.)
│
├── ast_convert_stmt.spl      (~600 lines)
│   - convert_statement dispatcher
│   - All statement converters (let, var, if, match, for, while, loop)
│   - Function/struct/enum/impl definitions
│   - Pattern converters
│
├── ast_convert_expr.spl      (~600 lines)
│   - convert_expression dispatcher
│   - All expression converters (binary, unary, call, method)
│   - Literal, array, dict, tuple converters
│   - Lambda, if-expr, match-expr, range
│
└── ast_convert.spl           (~20 lines)
    - Re-export module
```

**Benefits**:
- Types isolated for reuse
- Statement vs expression conversion separated
- Each file ~600 lines

---

## Phase 2.1: High Priority Files (P1)

### 4. packaging.spl (1249 lines → 3 files)

**Location**: `src/lib/std/src/tooling/deployment/packaging.spl`

**Proposed Split**:
```
packaging_formats.spl     (~450 lines) - Deb, RPM, pkg format handlers
packaging_metadata.spl    (~400 lines) - Package metadata, manifests
packaging_builder.spl     (~400 lines) - Build orchestration
packaging.spl             (~20 lines)  - Re-export
```

---

### 5. net/types.spl (1242 lines → 2 files)

**Location**: `src/lib/std/src/host/common/net/types.spl`

**Proposed Split**:
```
net_types_core.spl        (~650 lines) - Core network types
net_types_protocols.spl   (~600 lines) - Protocol-specific types
net/types.spl             (~20 lines)  - Re-export
```

---

### 6. mcp/advanced.spl (1219 lines → 2 files)

**Location**: `src/lib/std/src/mcp/advanced.spl`

**Proposed Split**:
```
mcp_advanced_features.spl (~650 lines) - Advanced MCP features
mcp_advanced_tools.spl    (~600 lines) - Tool implementations
mcp/advanced.spl          (~20 lines)  - Re-export
```

---

## Phase 2.2: Medium Priority Files (P2)

### 7. dependency.spl (1200 lines → 2 files)
**Location**: `src/lib/std/src/tooling/core/dependency.spl`
**Split**: dependency_resolver.spl (~650), dependency_graph.spl (~550)

### 8. test_runner_new/main.spl (1058 lines → 2 files)
**Location**: `src/app/test_runner_new/main.spl`
**Split**: test_runner.spl (~600), test_reporters.spl (~460)

### 9. project.spl (1055 lines → 2 files)
**Location**: `src/lib/std/src/tooling/core/project.spl`
**Split**: project_config.spl (~550), project_builder.spl (~500)

### 10. build_system.spl (944 lines)
**Location**: `src/lib/std/src/tooling/compiler/build_system.spl`
**Split**: build_graph.spl (~500), build_executor.spl (~450)

---

## Phase 2.3: Low Priority Files (P3)

**18 files in range 800-999 lines**

### Evaluation Criteria:
- **Keep as-is** if:
  - File is a test spec (comprehensive coverage expected)
  - File has cohesive single responsibility
  - Split would create artificial boundaries

- **Refactor** if:
  - Clear natural boundaries exist
  - File mixes multiple concerns
  - Splitting improves maintainability

### Files to Assess:

| File | Lines | Keep/Refactor | Reason |
|------|-------|---------------|--------|
| debug_spec.spl | 1578 | **Refactor** | Test file but very large, can split by feature |
| dim_constraints_spec.spl | 1191 | Keep | Comprehensive test suite |
| easy_fix_rules_spec.spl | 898 | Keep | Test suite, acceptable size |
| rust.spl | 978 | Keep | MCP rust integration, cohesive |
| tensor_dimensions.spl | 957 | Keep | Verification model, cohesive |
| errors.spl | 931 | Keep | Error types, single concern |
| term_style.spl | 918 | Keep | Terminal styling, cohesive |
| compiler_interface.spl | 912 | Keep | Interface definition, cohesive |
| reload.spl | 908 | Keep | Hot reload, single feature |
| bundling.spl | 908 | Keep | Bundling logic, cohesive |
| containers.spl | 896 | Keep | Container packaging, cohesive |
| array.spl | 884 | Keep | Core array implementation |
| primitives.spl | 872 | Keep | Core primitives, foundational |
| automation.spl | 866 | Keep | Deployment automation |
| expressions.spl | 816 | Keep | Lean expressions, cohesive |
| versioning.spl | 814 | Keep | Version management |
| json.spl | 803 | Keep | JSON parser, cohesive |
| actor_scheduler.spl | 841 | Keep | Async scheduler, single concern |

**Recommendation**: Keep all P3 files as-is except debug_spec.spl

---

## Implementation Strategy

### Order of Execution

**Phase 2.0 (Critical - Execute First)**:
1. mocking.spl (1905 → 3 files) - Highest impact
2. regex.spl (1408 → 3 files) - Core functionality
3. ast_convert.spl (1405 → 3 files) - App infrastructure

**Phase 2.1 (High Priority - If Time Permits)**:
4. packaging.spl (1249 → 3 files)
5. net/types.spl (1242 → 2 files)
6. mcp/advanced.spl (1219 → 2 files)

**Phase 2.2 (Medium Priority - Optional)**:
7. dependency.spl (1200 → 2 files)
8. test_runner_new/main.spl (1058 → 2 files)
9. project.spl (1055 → 2 files)
10. build_system.spl (944 → 2 files)

**Phase 2.3 (Low Priority - Skip)**:
- Keep all files as-is (acceptable sizes)

---

## Verification Steps

After each file split:

1. **Build Test**: `cargo build` must pass
2. **Import Test**: Verify all importers use re-export module
3. **Runtime Test**: Run relevant test suites
4. **Line Count**: Confirm all new files ≤800 lines

---

## Git/JJ Strategy

For each file split:
```bash
# 1. Create new files with extracted code
# 2. Update original file (remove extracted sections, add imports)
# 3. Update original to re-export new modules
# 4. Test build
# 5. Commit with message format:

jj commit -m "refactor(stdlib/app): Split {file} into {N} modules

Extract {concerns} from {file}:
- {module1}.spl ({lines} lines) - {description}
- {module2}.spl ({lines} lines) - {description}
- {original}.spl ({lines} lines) - Re-export module

Result: {file} reduced from {old} to {new} lines ({pct}% reduction)

Part of Phase 2 refactoring initiative.

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"

# 6. Push after each successful refactoring
jj bookmark set main -r @
jj git push --bookmark main
```

---

## Expected Results

### Phase 2.0 (Critical Files)

| Original | Lines | New Files | Max Lines | Total Lines | Reduction |
|----------|-------|-----------|-----------|-------------|-----------|
| mocking.spl | 1905 | 3 + re-export | 650 | ~1920 | 66% max file |
| regex.spl | 1408 | 3 + re-export | 590 | ~1430 | 58% max file |
| ast_convert.spl | 1405 | 3 + re-export | 600 | ~1420 | 57% max file |

**Impact**: Eliminate all files >1400 lines

### Phase 2.1 (High Priority)

| Original | Lines | New Files | Max Lines | Reduction |
|----------|-------|-----------|-----------|-----------|
| packaging.spl | 1249 | 3 | 450 | 64% max file |
| net/types.spl | 1242 | 2 | 650 | 48% max file |
| mcp/advanced.spl | 1219 | 2 | 650 | 47% max file |

**Impact**: Eliminate all files >1200 lines

### Phase 2.2 (Medium Priority)

**Impact**: 4 files reduced, all under 650 lines per file

### Overall Phase 2 Results (if all completed)

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Files >1400 lines | 3 | 0 | **-100%** |
| Files >1200 lines | 6 | 0 | **-100%** |
| Files >1000 lines | 10 | 0 | **-100%** |
| Files >800 lines | 34 | ~18 | **-47%** |
| New modular files | 0 | ~30 | +30 |

---

## Success Criteria

✅ **Phase 2.0 Complete** (Minimum Goal):
- All 3 critical files (>1400 lines) refactored
- Each new file ≤650 lines
- All builds pass
- No circular dependencies

✅ **Phase 2.1 Complete** (Target Goal):
- Phase 2.0 + all 3 high-priority files refactored
- All files >1200 lines eliminated
- Established patterns for stdlib refactoring

✅ **Phase 2.2 Complete** (Stretch Goal):
- Phase 2.1 + all 4 medium-priority files refactored
- All files >1000 lines eliminated
- Comprehensive modularization

---

## Risks & Mitigations

### Risk: Breaking stdlib API contracts
**Mitigation**: Use re-export pattern, maintain backward compatibility

### Risk: Test dependencies on file structure
**Mitigation**: Update imports to use re-export modules

### Risk: Circular dependencies in stdlib
**Mitigation**: Careful dependency analysis before splitting

### Risk: Over-engineering small files
**Mitigation**: Only refactor P0-P1, keep P3 as-is

---

## Timeline Estimate

**Phase 2.0** (Critical): 3 files × 1.5 hours = 4.5 hours
**Phase 2.1** (High): 3 files × 1 hour = 3 hours
**Phase 2.2** (Medium): 4 files × 1 hour = 4 hours

**Total**: 11.5 hours for complete Phase 2

**Minimum**: 4.5 hours for Phase 2.0 only

---

## Notes

- **Test files**: Generally acceptable to be larger (comprehensive coverage)
- **Core libraries**: Prefer cohesion over arbitrary line limits
- **Stdlib modules**: More important to have clear API boundaries than strict line counts
- **Focus**: Prioritize files that are actively developed over stable code

---

## Appendix: Quick Reference

### Files by Size (Top 10)

1. mocking.spl - 1905 lines ⭐⭐⭐
2. debug_spec.spl - 1578 lines (test)
3. regex.spl - 1408 lines ⭐⭐
4. ast_convert.spl - 1405 lines ⭐⭐⭐
5. packaging.spl - 1249 lines ⭐
6. net/types.spl - 1242 lines ⭐
7. mcp/advanced.spl - 1219 lines ⭐
8. dependency.spl - 1200 lines
9. dim_constraints_spec.spl - 1191 lines (test)
10. hir_lowering.spl - 1148 lines (compiler, already done)

⭐⭐⭐ = P0 (Critical)
⭐⭐ = P0 (Critical)
⭐ = P1 (High Priority)

---

**Status**: Ready for implementation
**Next Step**: Execute Phase 2.0 (Critical Files)
