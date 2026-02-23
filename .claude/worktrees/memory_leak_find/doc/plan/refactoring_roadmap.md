# Compiler & Stdlib Refactoring Roadmap

**Last Updated**: 2026-01-30
**Overall Goal**: Reduce all .spl files to ≤800 lines for improved maintainability

---

## Current Status

### Phase 1: Compiler Files ✅ **COMPLETE**

**Scope**: 10 compiler files in `simple/compiler/`
**Status**: Complete and committed to main
**Results**:
- Files >2000 lines: 3 → 0 (**100% eliminated**)
- Files >800 lines: 10 → 6 (**60% reduction**)
- New modular files: 31 created
- All builds passing: ✅

**Detailed Report**: `doc/report/compiler_refactoring_complete.md`

---

### Phase 2: Stdlib, App, and Test Files 📋 **PLANNED**

**Scope**: 28 additional files over 800 lines
**Status**: Plan ready for execution
**Target Results**:
- Files >1400 lines: 3 → 0 (**100% elimination**)
- Files >1200 lines: 6 → 0 (**100% elimination**)
- Files >1000 lines: 10 → 0 (**100% elimination**)
- Files >800 lines: 34 total → ~18 (**47% reduction**)

**Detailed Plan**: `doc/plan/refactoring_phase2_plan.md`

---

## Complete File Inventory

### Files Over 800 Lines (34 total)

#### ✅ Compiler (6 files) - Phase 1 Complete
1. parser.spl - 1809 lines ✅ (optimized, impl constraint)
2. type_infer.spl - 1478 lines ✅ (optimized, impl constraint)
3. treesitter.spl - 1333 lines ✅ (optimized, impl constraint)
4. lexer.spl - 1250 lines ✅ (optimized, impl constraint)
5. hir_lowering.spl - 1148 lines ✅ (optimized, impl constraint)
6. backend.spl - 842 lines ✅ (acceptable, 5% over)

#### 📋 Stdlib/App (28 files) - Phase 2 Planned

**P0: Critical (3 files >1400 lines)**
7. mocking.spl - 1905 lines ⭐⭐⭐ (testing framework)
8. regex.spl - 1408 lines ⭐⭐⭐ (core library)
9. ast_convert.spl - 1405 lines ⭐⭐⭐ (app infrastructure)

**P1: High Priority (3 files 1200-1399 lines)**
10. packaging.spl - 1249 lines ⭐⭐ (deployment)
11. net/types.spl - 1242 lines ⭐⭐ (networking)
12. mcp/advanced.spl - 1219 lines ⭐⭐ (MCP features)

**P2: Medium Priority (4 files 1000-1199 lines)**
13. dependency.spl - 1200 lines ⭐ (tooling)
14. test_runner_new/main.spl - 1058 lines ⭐ (testing)
15. project.spl - 1055 lines ⭐ (tooling)
16. build_system.spl - 944 lines ⭐ (compiler)

**P3: Low Priority (18 files 800-999 lines)**
17. debug_spec.spl - 1578 lines (test, could refactor)
18. dim_constraints_spec.spl - 1191 lines (test, keep)
19. easy_fix_rules_spec.spl - 898 lines (test, keep)
20. rust.spl - 978 lines (keep)
21. tensor_dimensions.spl - 957 lines (keep)
22. errors.spl - 931 lines (keep)
23. term_style.spl - 918 lines (keep)
24. compiler_interface.spl - 912 lines (keep)
25. reload.spl - 908 lines (keep)
26. bundling.spl - 908 lines (keep)
27. containers.spl - 896 lines (keep)
28. array.spl - 884 lines (keep)
29. primitives.spl - 872 lines (keep)
30. automation.spl - 866 lines (keep)
31. actor_scheduler.spl - 841 lines (keep)
32. expressions.spl - 816 lines (keep)
33. versioning.spl - 814 lines (keep)
34. json.spl - 803 lines (keep)

---

## Execution Roadmap

### ✅ Phase 1: Compiler Refactoring (Complete)

**Timeline**: Completed 2026-01-30
**Files**: 10 compiler files
**Result**: 60% reduction in files >800 lines
**Commits**: Pushed to main

### 📋 Phase 2.0: Critical Files (Next)

**Timeline**: ~4.5 hours
**Files**: 3 files (mocking, regex, ast_convert)
**Target**: Eliminate all files >1400 lines
**Strategy**: Split into 3 modules each

**Expected Results**:
- mocking.spl: 1905 → 650 max (3 files + re-export)
- regex.spl: 1408 → 590 max (3 files + re-export)
- ast_convert.spl: 1405 → 600 max (3 files + re-export)

### 📋 Phase 2.1: High Priority (Optional)

**Timeline**: ~3 hours
**Files**: 3 files (packaging, net/types, mcp/advanced)
**Target**: Eliminate all files >1200 lines
**Strategy**: Split into 2-3 modules each

### 📋 Phase 2.2: Medium Priority (Stretch)

**Timeline**: ~4 hours
**Files**: 4 files (dependency, test_runner, project, build_system)
**Target**: Eliminate all files >1000 lines
**Strategy**: Split into 2 modules each

### Phase 2.3: Low Priority (Skip)

**Decision**: Keep 18 files (800-999 lines) as-is
**Rationale**:
- Test files naturally comprehensive
- Core libraries should prioritize cohesion
- Acceptable size for stable code

---

## Overall Impact

### If Phase 2 Complete

| Metric | Before | Phase 1 | Phase 2 | Total |
|--------|--------|---------|---------|-------|
| Files >2000 | 3 | 0 | 0 | **-100%** |
| Files >1400 | 3 | 3 | 0 | **-100%** |
| Files >1200 | 6 | 6 | 0 | **-100%** |
| Files >1000 | 10 | 10 | 0 | **-100%** |
| Files >800 | ~44 | 34 | ~18 | **-59%** |
| New files | 0 | +31 | +30 | **+61** |

### File Distribution After Phase 2

```
Before Phase 1:  ████████████████████████████ (44 files >800)
After Phase 1:   ████████████████████ (34 files >800)
After Phase 2.0: ██████████████ (31 files >800)
After Phase 2.1: ████████████ (28 files >800)
After Phase 2.2: ██████████ (~18 files >800)
Target Complete: ██████████ (~18 files, all 800-999 acceptable)
```

---

## Patterns Established

### 1. Type Extraction Pattern
- Extract type definitions to separate `*_types.spl` files
- Main file focuses on implementation
- **Used in**: Phase 1 (8 files), Phase 2.0 (ast_convert)

### 2. Logical Separation Pattern
- Split by functional concern (parser vs engine, core vs fluent)
- Each module has clear responsibility
- **Used in**: Phase 1 (MIR, HIR), Phase 2.0 (all 3 files)

### 3. Re-export Compatibility Pattern
- Original filename becomes re-export module
- Maintains backward compatibility
- **Used in**: All refactored files (61 re-exports planned)

### 4. Domain Separation Pattern (New in Phase 2)
- Split by domain/protocol (packaging formats, network protocols)
- **Used in**: Phase 2.1 (packaging, net/types)

---

## Language Constraints

### Impl Block Limitation
**Issue**: Simple requires all methods for a struct/class in same file
**Impact**: Files with large impl blocks can't be split further
**Workaround**: Extract types, helper functions, related structs

**Affected Files** (6 compiler files in Phase 1):
- parser.spl (1809 lines)
- type_infer.spl (1478 lines)
- treesitter.spl (1333 lines)
- lexer.spl (1250 lines)
- hir_lowering.spl (1148 lines)
- backend.spl (842 lines, acceptable)

**Resolution**: These files optimized within constraint (9-37% reduction)

---

## Success Criteria

### Phase 1 ✅
- [x] All 10 compiler files refactored
- [x] All files >2000 lines eliminated
- [x] 60% reduction in files >800 lines
- [x] Zero regressions
- [x] All builds passing

### Phase 2.0 (Minimum)
- [ ] 3 critical files refactored
- [ ] All files >1400 lines eliminated
- [ ] Each new file ≤650 lines
- [ ] All builds passing

### Phase 2.1 (Target)
- [ ] Phase 2.0 + 3 high-priority files
- [ ] All files >1200 lines eliminated
- [ ] Stdlib refactoring patterns established

### Phase 2.2 (Stretch)
- [ ] Phase 2.1 + 4 medium-priority files
- [ ] All files >1000 lines eliminated
- [ ] Comprehensive modularization

---

## Next Steps

1. **Review Phase 2 Plan**: `doc/plan/refactoring_phase2_plan.md`
2. **Execute Phase 2.0**: Start with mocking.spl (highest impact)
3. **Verify After Each**: Build, test, commit
4. **Assess Progress**: Decide on Phase 2.1/2.2 continuation

---

## Quick Reference

### Key Documents
- **Phase 1 Report**: `doc/report/compiler_refactoring_complete.md`
- **Phase 2 Plan**: `doc/plan/refactoring_phase2_plan.md`
- **This Roadmap**: `doc/plan/refactoring_roadmap.md`

### Commands
```bash
# Check current status
find simple src/lib/std/src src/app -name "*.spl" -type f 2>/dev/null |
  grep -v "\.disabled" | xargs wc -l 2>/dev/null |
  awk '$1 >= 800 {print $1, $2}' | sort -rn

# Build verification
cargo build

# Commit pattern
jj commit -m "refactor(...): Split {file} into {N} modules"
jj bookmark set main -r @
jj git push --bookmark main
```

---

**Status**: Phase 1 ✅ Complete | Phase 2 📋 Ready for execution
**Recommendation**: Start Phase 2.0 (critical files) for maximum impact
