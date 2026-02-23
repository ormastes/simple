# Remaining Work Plan - Simple Language Compiler

**Date:** 2026-02-13
**Status:** Active Planning

---

## Executive Summary

**806 TODOs** across codebase, **269 tracked** in TODO.md.
**78 stdlib utils files** need refactoring (averaging 1,100 lines each).
**10 large compiler files** documented as technical debt (cannot split impl blocks yet).

---

## 1. Stdlib Refactoring (IN PROGRESS)

### Status: ~30% Complete

**Already Refactored:**
- ✅ `avro/` - 7 modules created
- ✅ `b_tree/` - 8 modules created  
- ✅ `compression/gzip/` - 9 modules created
- ✅ `crypto/` - 7 modules created
- ✅ `file_system/` - 8 modules created
- ✅ `graph/` - 9 modules created
- ✅ `html/` - 7 modules created
- 🚧 `json/` - In progress (2,240 lines → 8 modules)

**Remaining Priority 1 (Critical: 2000+ lines):**
- [ ] `numerical_methods_utils.spl` (2,434 lines) → 11 modules
- [ ] Complete `json_parser_utils.spl` split
- [ ] Verify all existing splits pass tests

**Remaining Priority 2 (High: 1500-2000 lines):**
- [ ] `b_tree_utils.spl` (1,847) - Already started?
- [ ] `fenwick_tree_utils.spl` (1,792)
- [ ] `html_parser_utils.spl` (1,769) - Already started?
- [ ] `red_black_tree_utils.spl` (1,764)
- [ ] `rsa_utils.spl` (1,759)
- [ ] `avro_utils.spl` (1,738) - Already started?
- [ ] `file_system_utils.spl` (1,695) - Already started?
- [ ] `regex_engine_utils.spl` (1,686)
- [ ] `crypto_utils.spl` (1,677) - Already started?
- [ ] `optimization_utils.spl` (1,664)

**Remaining Priority 3 (Medium: 1200-1500 lines):**
- 18 files pending

**Remaining Priority 4 (Standard: 800-1200 lines):**
- 46 files pending

### Implementation Strategy

**Phase 1 (Current):** Prove pattern with largest files
- Target: Critical 2000+ line files
- Status: ~40% complete (4 of ~10 started)

**Phase 2 (Next 2 weeks):** High priority files
- Target: 1500-2000 line files (10 files)
- Parallel execution possible

**Phase 3 (Following month):** Medium/standard priority
- Target: 800-1500 line files (64 files)
- Batch processing

---

## 2. TODO Items by Category

### Total: 806 TODOs in source code

**Breakdown by type:**

#### Stub Implementations (~100 items)
Files with `stub`, `STUB`, `NotImplemented`, `todo()`:
- `src/compiler/linker/` - SMF format stubs
- `src/compiler/loader/` - JIT/cache stubs  
- `src/compiler/backend/` - Backend stubs
- `src/compiler/mir_opt/` - Optimization stubs

**Action:** Prioritize by user-facing impact:
1. SMF loader integration (blocks native compilation)
2. Backend implementations (affects performance)
3. MIR optimizations (nice-to-have)

#### FFI Placeholders (~50 items)
- Process management (spawn, limits)
- File system operations (mmap, watch)
- Platform-specific APIs (Windows timeout)

**Action:** Group by platform and implement via SFFI

#### Parser/Language Limitations (~20 items)
- Static method calls in interpreter
- Generic type support at runtime
- Multi-line boolean expressions

**Action:** Language runtime improvements needed

#### Re-enable When Ready (~30 items)
Code commented out waiting for:
- Collection modules complete
- AST construction fixes
- Module import fixes

**Action:** Track with feature completion

---

## 3. Technical Debt (Cannot Fix Yet)

### Large Impl Blocks - 10 files

**Reason:** Simple doesn't support splitting impl blocks across files

| File | Lines | Type |
|------|-------|------|
| `compiler/parser.spl` | 2,453 | impl Parser |
| `compiler_core_legacy/parser.spl` | 2,322 | impl Parser |
| `app/compile/c_translate.spl` | 1,871 | impl CTranslator |
| `compiler_core_legacy/parser.spl` | 1,862 | impl Parser |
| `app/mcp/main.spl` | 1,854 | MCP orchestration |
| `compiler/treesitter/outline.spl` | 1,823 | impl TreeSitter |
| `compiler_core_legacy/interpreter/eval.spl` | 1,619 | impl Interpreter |
| `compiler/mir_lowering.spl` | 1,503 | impl MirLowering |
| `compiler/lexer.spl` | 1,430 | impl Lexer |

**Total:** ~19,000 lines of large impl blocks

**Action:** Document per CLAUDE.md guidelines:
- Add comment explaining why file is large
- Link to language feature tracking issue
- Keep well-organized with section comments

---

## 4. Test Coverage

### Skipped/Pending Tests

Found via `bin/simple test --list`:
- `test/feature/parser_skip_*.spl` - Parser skip policies
- Various integration tests marked as skip

**Action:** 
1. Review each skip reason
2. Categorize: language limitation vs implementation gap
3. Create tracking issues for implementation gaps

---

## 5. Feature Completion Status

**Pending Features:** Check `doc/feature/pending_feature.md`

**Categories to review:**
1. Parser features (syntax additions)
2. Type system features (generics, traits)
3. Runtime features (async, actors)
4. Backend features (LLVM, native)
5. Stdlib features (missing modules)

---

## 6. Recommended Work Order

### Week 1-2: Complete Critical Stdlib Refactoring
1. ✅ Verify existing splits (avro, b_tree, crypto, etc.)
2. 🚧 Complete `json/` split (in progress)
3. [ ] Refactor `numerical_methods_utils.spl` (largest)
4. [ ] Run full test suite on all refactored modules

### Week 3-4: High Priority Stdlib Refactoring  
5. [ ] Refactor 10 high-priority utils files (1500-2000 lines)
6. [ ] Document pattern for future contributors
7. [ ] Create automated refactoring tool if pattern is clear

### Month 2: Stub Implementations
8. [ ] Group TODOs by feature area
9. [ ] Implement SMF loader (highest priority)
10. [ ] Implement critical FFI functions
11. [ ] Fill in backend stubs

### Month 3: Test Coverage & Features
12. [ ] Review all skipped tests
13. [ ] Implement missing test features
14. [ ] Complete pending features from feature DB

### Ongoing: Technical Debt Documentation
15. [ ] Add explanatory comments to large impl blocks
16. [ ] Create language feature request for split impl blocks
17. [ ] Document architectural decisions in large files

---

## 7. Metrics & Tracking

### Current State (2026-02-13)
- **TODOs:** 806 total, 269 tracked
- **Stdlib utils:** 78 files, ~30% refactored
- **Large files:** 10 impl blocks documented
- **Test coverage:** TBD (run coverage analysis)

### Target State (Q2 2026)
- **TODOs:** <500 total, all tracked
- **Stdlib utils:** 100% refactored
- **Large files:** All documented with comments
- **Test coverage:** >80% for refactored code

---

## 8. Quick Action Items (Next 7 Days)

### High Priority
1. [ ] Verify all existing stdlib splits compile and pass tests
2. [ ] Complete `json/` module split (in progress)
3. [ ] Create TODO categorization script
4. [ ] Run test coverage analysis on refactored modules

### Medium Priority  
5. [ ] Document large impl block policy in CLAUDE.md
6. [ ] Create stub implementation tracking issue
7. [ ] Review pending features list

### Low Priority
8. [ ] Create automated refactoring helper script
9. [ ] Set up CI check for file size limits
10. [ ] Document SFFI patterns for FFI TODOs

---

## 9. Risks & Mitigation

### Risk: Breaking Changes from Refactoring
**Mitigation:** 
- Maintain facade pattern (old imports work)
- Run full test suite before/after each refactor
- Use version control (jj) for easy rollback

### Risk: Stub Implementations Block Features
**Mitigation:**
- Prioritize stubs by user impact
- Create tracking issues for each stub area
- Document workarounds for users

### Risk: Large Files Remain Technical Debt
**Mitigation:**
- Document clearly in code comments
- Create language feature proposal for split impl
- Keep files well-organized internally

---

## 10. Success Criteria

### Stdlib Refactoring Complete
- ✅ All utils files split into <400 line modules
- ✅ All imports continue working (facade pattern)
- ✅ All tests pass
- ✅ Documentation updated

### TODO Backlog Managed
- ✅ All TODOs categorized
- ✅ Critical TODOs tracked with issues
- ✅ Implementation plan exists

### Technical Debt Documented
- ✅ Large files have explanatory comments
- ✅ Language limitations documented
- ✅ Architectural decisions recorded

---

## Notes

- **Version Control:** Use jj (NOT git), work on main
- **Testing:** NEVER skip tests without user approval
- **Code Style:** Minimal changes, no over-engineering
- **Documentation:** Update as we refactor

---

**Next Review:** 2026-02-20 (weekly check-in)
**Owner:** Development team
**Last Updated:** 2026-02-13
