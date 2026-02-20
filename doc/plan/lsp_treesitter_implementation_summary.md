# LSP & Treesitter Implementation Summary

**Date:** 2026-02-05
**Status:** 📋 Design Complete - Ready to Implement
**Impact:** +91 tests (LSP: 80, Treesitter: 11)

---

## ✅ What's Been Completed

### 1. **Comprehensive Analysis** ✅

**Analyzed Failures:**
- LSP: 80 tests (0/80 passing)
  - Lifecycle: 17 tests
  - Document Sync: 18 tests
  - Features: 45 tests (completion, hover, definitions, etc.)
- Treesitter: 11 tests (0/11 passing)
  - Core: 5 tests (parsing, navigation)
  - Queries: 6 tests (pattern matching)

**Identified Requirements:**
- Pure Simple implementation with SFFI wrappers
- Two-tier pattern: extern FFI → Simple wrappers → business logic
- 40+ FFI functions needed for treesitter
- Minimal FFI surface for performance

### 2. **Complete Architecture Design** ✅

**Designed Components:**

```
┌─────────────────────────────────┐
│      LSP Server (Pure Simple)   │
│  • Lifecycle mgmt               │
│  • Document sync                │
│  • Code intelligence handlers   │
└────────────┬────────────────────┘
             │
             ▼
┌─────────────────────────────────┐
│   Treesitter (Simple + SFFI)    │
│  • Parser wrapper               │
│  • Tree/Node navigation         │
│  • Query system                 │
└────────────┬────────────────────┘
             │
             ▼
┌─────────────────────────────────┐
│    SFFI Runtime (Minimal Rust)  │
│  • 40+ rt_ts_* functions        │
│  • Handle management            │
│  • C library bridge             │
└─────────────────────────────────┘
```

**Key Design Decisions:**
- ✅ Two-tier SFFI pattern (matches project standard)
- ✅ Pure Simple for all business logic
- ✅ Minimal FFI surface (performance-critical only)
- ✅ Handle-based API (no raw pointers in Simple)
- ✅ Incremental parsing support
- ✅ Query result caching

### 3. **Detailed Implementation Plan** ✅

**Created Documents:**
- `doc/plan/lsp_treesitter_sffi_implementation_plan.md` (350+ lines)
  - Full architecture diagrams
  - API specifications
  - Code examples for all components
  - Sprint breakdown (6 sprints, 21 days)
  - Success metrics
  - Build & test commands

### 4. **SFFI Specification** ✅

**Created:** `src/app/ffi_gen/specs/treesitter.spl`

**Contents:**
- 40+ extern function declarations
- Complete documentation for each function
- Organized into logical sections:
  - Parser management (3 functions)
  - Parsing operations (2 functions)
  - Tree management (3 functions)
  - Node operations - type/position (6 functions)
  - Node operations - navigation (7 functions)
  - Node operations - properties (5 functions)
  - Query operations (5 functions)
  - Query cursor operations (6 functions)

**Ready for Generation:**
```bash
simple sffi-gen --gen-intern src/app/ffi_gen/specs/treesitter.spl
```

---

## 📋 Implementation Roadmap (21 Days)

### **Sprint 1: Treesitter Core** (Days 1-3)
- Generate SFFI bindings
- Implement Simple wrappers (`TreeSitterParser`, `Tree`, `Node`)
- Test basic parsing
- **Goal:** 5/11 treesitter tests passing

### **Sprint 2: Treesitter Queries** (Days 4-5)
- Implement `Query` and `QueryCursor` wrappers
- Test pattern matching
- **Goal:** 6/11 treesitter tests passing (all passing)

### **Sprint 3: LSP Lifecycle** (Days 6-8)
- Complete `LspServer` class
- Implement initialize/shutdown flow
- **Goal:** 17/80 LSP tests passing

### **Sprint 4: Document Sync** (Days 9-11)
- Implement didOpen/didChange/didClose
- Add incremental parsing
- **Goal:** 35/80 LSP tests passing (+18)

### **Sprint 5: Code Intelligence** (Days 12-18)
- Completion (11 tests) - Days 12-13
- Hover (5 tests) - Day 14
- Definition (5 tests) - Day 15
- References (5 tests) - Day 16
- Diagnostics (9 tests) - Days 17-18
- Semantic Tokens (10 tests) - Days 17-18
- **Goal:** 80/80 LSP tests passing (all passing)

### **Sprint 6: Polish** (Days 19-21)
- Add query caching
- Add debouncing
- Performance optimization
- **Goal:** All 91 tests passing, production ready

---

## 📁 Files Created

### Planning Documents
1. ✅ `doc/plan/lsp_treesitter_sffi_implementation_plan.md`
   - 350+ lines of detailed design
   - Architecture diagrams
   - API specifications
   - Sprint breakdown
   - Success metrics

2. ✅ `doc/plan/lsp_treesitter_implementation_summary.md` (this file)
   - Executive summary
   - Quick reference
   - Next steps

### SFFI Specifications
3. ✅ `src/app/ffi_gen/specs/treesitter.spl`
   - 40+ FFI function declarations
   - Complete documentation
   - Ready for code generation

---

## 🚀 Next Steps (Immediate Actions)

### Step 1: Generate SFFI Bindings
```bash
cd /home/ormastes/dev/pub/simple
simple sffi-gen --gen-intern src/app/ffi_gen/specs/treesitter.spl
```

This generates: `build/rust/ffi_gen/src/treesitter.rs`

### Step 2: Implement Simple Wrappers
Create: `src/lib/src/parser/treesitter.spl`

**Structure:**
```simple
export TreeSitterParser, Tree, Node, Query, QueryCursor

class TreeSitterParser:
    _handle: i64
    language: text
    # ... methods using rt_ts_* functions

class Tree:
    _handle: i64
    source: text
    # ... methods

class Node:
    _handle: i64
    tree: Tree
    # ... methods

# ... etc
```

### Step 3: Add Extern Declarations
Update: `src/app/io/mod.spl`

Add exports:
```simple
export rt_ts_parser_new, rt_ts_parser_parse, rt_ts_tree_root_node
# ... all 40+ functions
```

### Step 4: Run Tests
```bash
# Test treesitter core
simple test test/lib/std/unit/parser/treesitter*.spl

# Test LSP
simple test test/lib/std/unit/lsp/*.spl
```

---

## 📊 Expected Impact

### Test Improvement
| Component | Before | After | Impact |
|-----------|--------|-------|--------|
| Treesitter | 0/11 | 11/11 | +11 ✅ |
| LSP | 0/80 | 80/80 | +80 ✅ |
| **Total** | **0/91** | **91/91** | **+91 tests** |

### Pass Rate Improvement
```
Current:  89.1% (6436/7222 passing)
Target:   90.4% (6527/7222 passing)
Gain:     +1.3% (+91 tests)
```

### Implementation Time
- **Estimated:** 21 days (3 weeks)
- **Risk:** Low (design complete, pattern proven)
- **Complexity:** Medium (mostly wrapper code)

---

## 🎯 Success Criteria

### Phase Completion Checklist

- [ ] **Sprint 1 Complete** - Treesitter core working (5 tests)
- [ ] **Sprint 2 Complete** - Treesitter queries working (6 tests)
- [ ] **Sprint 3 Complete** - LSP lifecycle working (17 tests)
- [ ] **Sprint 4 Complete** - Document sync working (18 tests)
- [ ] **Sprint 5 Complete** - All features working (45 tests)
- [ ] **Sprint 6 Complete** - Production ready (91 tests)

### Performance Targets

| Metric | Target |
|--------|--------|
| Parse time (1000 lines) | < 50ms |
| Incremental parse | < 10ms |
| Completion latency | < 100ms |
| Memory per document | < 5MB |

---

## 🔑 Key Insights

### Why This Will Work

1. **Two-Tier Pattern Proven** ✅
   - Already used throughout codebase
   - See: random.spl, time.spl, file I/O
   - Pattern is stable and maintainable

2. **Minimal FFI Surface** ✅
   - Only 40 functions needed
   - All handle-based (no pointer juggling)
   - Clear ownership model

3. **Pure Simple Business Logic** ✅
   - LSP handlers entirely in Simple
   - Easy to maintain and extend
   - Fast iteration cycle

4. **Incremental Approach** ✅
   - Each sprint delivers working tests
   - Can pause/resume at any point
   - Risk is distributed

5. **Clear Success Metrics** ✅
   - Test count is objective measure
   - Each phase has concrete deliverable
   - Easy to track progress

### Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| SFFI generation fails | Manual Rust impl (fallback) |
| Performance issues | Add caching layer (Sprint 6) |
| Complex edge cases | Incremental approach allows fixes |
| Test infrastructure issues | Fix infrastructure first |

---

## 📚 Reference Materials

### Key Files to Study

**Existing Patterns:**
- `src/app/interpreter.extern/random.spl` - SFFI wrapper example
- `src/app/interpreter.extern/time.spl` - Handle-based FFI
- `src/app/io/mod.spl` - Extern declarations pattern

**Existing LSP Code:**
- `src/app/lsp/server.spl` - Server skeleton (needs completion)
- `src/app/lsp/protocol.spl` - LSP types
- `src/app/lsp/transport.spl` - JSON-RPC transport

### External Resources

**Tree-sitter:**
- C API: https://tree-sitter.github.io/tree-sitter/using-parsers
- Rust bindings: https://docs.rs/tree-sitter/latest/tree_sitter/

**LSP:**
- Protocol spec: https://microsoft.github.io/language-server-protocol/
- Capabilities: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#initialize

---

## 🎉 Summary

**What We Have:**
- ✅ Complete analysis of requirements (91 tests)
- ✅ Detailed architecture design
- ✅ Implementation plan (6 sprints, 21 days)
- ✅ SFFI specification (40+ functions)
- ✅ Clear success metrics
- ✅ Risk mitigation strategies

**What We Need:**
- [ ] Generate SFFI bindings
- [ ] Implement Simple wrappers
- [ ] Complete LSP handlers
- [ ] Test & iterate

**Confidence Level:** 🟢 High
- Design is solid
- Pattern is proven
- Plan is detailed
- Path is clear

**Ready to Start:** ✅ YES

---

**Document Status:** ✅ Complete
**Next Action:** Generate SFFI bindings
**Command:** `simple sffi-gen --gen-intern src/app/ffi_gen/specs/treesitter.spl`
