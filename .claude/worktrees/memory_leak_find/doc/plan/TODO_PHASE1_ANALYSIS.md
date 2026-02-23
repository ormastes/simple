# TODO Phase 1: Critical Stub Implementations - Analysis

**Date:** 2026-02-13 00:51 UTC
**Status:** Analysis Phase

---

## Phase 1 Overview

**Scope:** ~100 critical TODOs blocking major features
**Focus Areas:**
1. SMF Loader Integration
2. Backend Stubs  
3. Compiler Integration Stubs

**Impact:** Enables native compilation, linking, and packaging

---

## 1. SMF Loader Integration (Highest Priority)

### What is SMF?

**SMF = Simple Module Format**
- Binary format for compiled Simple modules
- Similar to ELF/Mach-O but simpler
- Contains: code, data, symbols, relocations, templates
- Enables: separate compilation, linking, packaging

### Current Status

**Implementation:** Partial stubs exist
**Blocking:** Native compilation pipeline, packaging system

### Files Involved (7 files, ~15 TODOs)

| File | Lines | TODOs | Purpose |
|------|-------|-------|---------|
| `linker/smf_header.spl` | ? | ? | Parse SMF file headers |
| `linker/smf_reader.spl` | ? | ? | Read SMF sections |
| `linker/smf_reader_memory.spl` | ? | ? | In-memory SMF reading |
| `linker/lazy_instantiator.spl` | ? | ? | Lazy template instantiation |
| `linker/object_resolver.spl` | ? | ? | Resolve symbols between objects |
| `loader/jit_instantiator.spl` | ? | ? | JIT compilation from SMF |
| `loader/smf_cache.spl` | ? | ? | Cache compiled SMF modules |

### Key TODOs Identified

```
src/compiler/linker/smf_header.spl:
- [ ] Implement actual SMF header parsing
- [ ] Implement section table reading

src/compiler/linker/smf_reader.spl:
- [ ] Implement proper template parsing
- [ ] Create SmfReaderImpl from in-memory data

src/compiler/linker/lazy_instantiator.spl:
- [ ] Load actual templates from SMF TemplateCode sections

src/compiler/loader/jit_instantiator.spl:
- [ ] Load actual template bytes from SMF
- [ ] Compile via FFI (needs JSON serialization)
- [ ] Implement proper SMF update

src/compiler/loader/smf_cache.spl:
- [ ] Parse section table for accurate offsets
- [ ] Read actual section data
```

### Implementation Strategy

**Option A: Implement in Simple** (Recommended)
- Pure Simple implementation
- No external dependencies
- Easier to debug and maintain
- Slower but acceptable for compilation

**Option B: FFI to Runtime**
- C/Rust implementation for speed
- Faster parsing
- Harder to maintain
- Overkill for most use cases

**Option C: Hybrid**
- Simple for structure/logic
- FFI for performance-critical sections only
- Best of both worlds
- More complex

**Recommendation: Option A** - Start pure Simple, optimize later if needed

---

## 2. Backend Stubs (~20 TODOs)

### Files Involved

| File | TODOs | Purpose |
|------|-------|---------|
| `backend/interpreter.spl` | ~12 | String ptr/len conversions |
| `backend.spl` | ~5 | Re-enable commented backends |
| `backend/exhaustiveness_validator.spl` | 1 | Filesystem FFI |

### Key Issues

**String Conversion (9 instances):**
```simple
# TODO: Proper string ptr+len conversion
# Currently stub implementations
```

**Backend Re-enabling (3 instances):**
```simple
# TODO: Backends commented out due to parse errors
# - Cranelift backend
# - LLVM backend  
# - Native backend
```

### Implementation Strategy

1. **Fix runtime parser bugs** - Root cause of commented code
2. **Implement string helpers** - Proper ptr+len ↔ Simple string
3. **Re-enable backends** - One at a time, test each
4. **Test end-to-end** - Verify compilation works

---

## 3. Compiler Integration Stubs (~15 TODOs)

### Files Involved

| File | TODOs | Purpose |
|------|-------|---------|
| `compiler/init.spl` | 1 | Actual parsing implementation |
| `compiler/build_native.spl` | 1 | FFI implementation |
| `loader/compiler_ffi.spl` | 6 | Real code gen, type checking, JSON |

### Key Issues

**Stub Implementations:**
```simple
# TODO: Implement actual parsing (not stub)
# TODO: Real code generation
# TODO: Real type checking
# TODO: Real JSON parsing
```

### Implementation Strategy

1. **Connect to actual compiler pipeline** - Remove stubs
2. **Implement JSON serialization** - For FFI communication
3. **Test compilation** - End-to-end verification
4. **Remove TODOs** - Delete stub comments

---

## Implementation Plan

### Week 1: SMF Foundation (Feb 13-20)

**Day 1-2: SMF Spec & Header**
- [ ] Document SMF format spec (if missing)
- [ ] Implement `smf_header.spl` - parse headers
- [ ] Implement section table parsing
- [ ] Test: Read SMF file headers

**Day 3-4: SMF Reader**
- [ ] Implement `smf_reader.spl` - read sections
- [ ] Implement template parsing
- [ ] Test: Read SMF sections

**Day 5: SMF Memory Reader**
- [ ] Implement `smf_reader_memory.spl`
- [ ] Test: Parse in-memory SMF data

**Day 6-7: Integration & Testing**
- [ ] End-to-end SMF reading test
- [ ] Document APIs
- [ ] Clean up TODOs

### Week 2: Backends & Integration (Feb 21-27)

**Day 1-2: String Conversion**
- [ ] Implement string ptr+len helpers
- [ ] Fix all 9 conversion TODOs
- [ ] Test string operations

**Day 3-4: Backend Re-enabling**
- [ ] Fix parser bugs blocking backends
- [ ] Re-enable Cranelift backend
- [ ] Re-enable LLVM backend
- [ ] Test each backend

**Day 5-7: Compiler Integration**
- [ ] Remove compilation stubs
- [ ] Implement JSON serialization
- [ ] Connect to real pipeline
- [ ] End-to-end testing

### Week 3: Cleanup & Documentation (Feb 28 - Mar 6)

**Day 1-2: Testing**
- [ ] Full test suite
- [ ] Integration tests
- [ ] Performance tests

**Day 3-4: Documentation**
- [ ] SMF format documentation
- [ ] API documentation
- [ ] Usage examples

**Day 5: Cleanup**
- [ ] Remove all Phase 1 TODOs
- [ ] Update TODO.md
- [ ] Mark Phase 1 complete

---

## Success Criteria

### Phase 1 Complete When:
- ✅ SMF files can be read and parsed
- ✅ Sections extracted correctly
- ✅ Templates loaded and instantiated
- ✅ All backends re-enabled
- ✅ String conversions working
- ✅ Compiler stubs replaced with real implementations
- ✅ All ~100 Phase 1 TODOs removed
- ✅ Tests passing
- ✅ Documentation complete

---

## Risks & Mitigation

### Risk: SMF Format Undocumented
**Mitigation:** 
- Review existing code for format clues
- Check test files for examples
- Document as we implement

### Risk: Parser Bugs Block Backends
**Mitigation:**
- Fix parser bugs first
- Test incrementally
- Keep backends separate

### Risk: FFI Dependencies
**Mitigation:**
- Implement in pure Simple first
- Add FFI only if performance needed
- Keep FFI interface small

---

## Next Actions (Immediate)

1. ✅ Analyze SMF TODO locations (DONE)
2. [ ] Find or create SMF format specification
3. [ ] List all SMF-related TODOs with line numbers
4. [ ] Create file-by-file implementation plan
5. [ ] Start with smf_header.spl implementation

---

**Estimated Total Time:** 3 weeks (15 working days)
**Current Phase:** Analysis
**Next Phase:** SMF Spec & Header Implementation
