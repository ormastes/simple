# TODO Items - Phased Implementation Plan

**Created:** 2026-02-13
**Status:** Active
**Total TODOs:** 806 in source code, 269 tracked

---

## Strategy: Categorize, Prioritize, Implement, Delete

**After each TODO fixed:**
1. Implement the feature/fix
2. Remove the TODO comment
3. Add tests if needed
4. Commit: `jj describe -m "fix: Implement <feature>"`
5. Mark item complete in this document

---

## Progress Tracker

| Phase | TODOs | Status |
|-------|-------|--------|
| Phase 1 | ~100 | 📋 PLANNED - SMF & FFI stubs |
| Phase 2 | ~50 | 📋 PLANNED - FFI functions |
| Phase 3 | ~30 | 📋 PLANNED - Re-enable code |
| Phase 4 | ~20 | 📋 PLANNED - Parser limitations |
| Phase 5 | ~606 | 📋 PLANNED - General TODOs |

---

## Phase 1: Critical Stub Implementations (~100 items)

**Timeline:** Month 2 (Mar 2026)
**Priority:** P0 - Blocks features

### 1.1 SMF Loader Integration (Highest Priority)

**Impact:** Blocks native compilation, linking, packaging

**Files affected:**
- `src/compiler/linker/*.spl` (15 TODOs)
- `src/compiler/loader/*.spl` (12 TODOs)

**TODOs:**
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

**Implementation steps:**
1. Design SMF format spec (if not exists)
2. Implement parser in Simple
3. Add FFI functions for mmap if needed
4. Test with real SMF files
5. Delete all related TODOs
6. Commit

---

### 1.2 Backend Stubs (20 TODOs)

**Files affected:**
- `src/compiler/backend/*.spl`

**TODOs:**
```
src/compiler/backend/interpreter.spl:
- [ ] Proper string ptr+len conversion (9 instances)
- [ ] Convert ptr to Simple string (2 instances)
- [ ] Full conversion for Array, Dict, etc.

src/compiler/backend.spl:
- [ ] Fix parse errors in backend/*.spl
- [ ] Re-enable commented out backends (Cranelift, LLVM, Native)
```

**Implementation steps:**
1. Fix runtime parser bugs blocking backend files
2. Implement string conversion helpers
3. Re-enable backends one by one
4. Test each backend
5. Delete TODOs

---

### 1.3 Compiler Integration Stubs (15 TODOs)

**Files affected:**
- `src/compiler/init.spl`
- `src/compiler/build_native.spl`
- `src/compiler/loader/compiler_ffi.spl`

**TODOs:**
```
src/compiler/init.spl:
- [ ] Implement actual parsing (not stub)

src/compiler/build_native.spl:
- [ ] Implement via FFI

src/compiler/loader/compiler_ffi.spl:
- [ ] Real code generation
- [ ] Real type checking
- [ ] Real JSON parsing (3 instances)
```

**Implementation steps:**
1. Connect to actual compiler pipeline
2. Implement JSON serialization for FFI
3. Test end-to-end compilation
4. Delete TODOs

---

## Phase 2: FFI Function Implementations (~50 items)

**Timeline:** Month 2-3 (Mar-Apr 2026)
**Priority:** P1 - Platform features

### 2.1 Process Management (10 TODOs)

**Files affected:**
- `src/app/io/mod.spl`

**TODOs:**
```
src/app/io/mod.spl:
- [ ] Implement Windows timeout using PowerShell or .NET
- [ ] Implement memory_bytes, cpu_seconds limits
- [ ] Implement max_fds, max_procs limits
- [ ] When rt_process_spawn_async available, run in parallel
```

**Implementation steps:**
1. Add SFFI declarations for process functions
2. Implement runtime functions in C/Rust
3. Add platform-specific implementations (Windows)
4. Test on all platforms
5. Delete TODOs

---

### 2.2 File System Operations (15 TODOs)

**TODOs:**
```
src/compiler/backend/exhaustiveness_validator.spl:
- [ ] Use filesystem FFI

src/compiler/loader/jit_instantiator.spl:
- [ ] Add mmap functions to app.io.mod (executable memory)

src/compiler/loader/smf_cache.spl:
- [ ] Add mmap functions to app.io.mod (memory-mapped files)

src/compiler/module_resolver/resolution.spl:
- [ ] Proper FFI functions for file operations
```

**Implementation steps:**
1. Design SFFI interface for file operations
2. Implement in runtime
3. Add to `src/app/io/mod.spl`
4. Test cross-platform
5. Delete TODOs

---

### 2.3 Platform-Specific APIs (10 TODOs)

**TODOs:**
```
src/app/io/mod.spl:
- [ ] Re-enable platform-specific command resolution
- [ ] Implement serial port reading (semihost)
- [ ] Implement OpenOCD GDB RSP connection
```

**Implementation steps:**
1. Identify platform-specific needs
2. Use SFFI three-tier pattern for external libs
3. Implement wrappers
4. Test on target platforms
5. Delete TODOs

---

### 2.4 Compiler Backend FFI (15 TODOs)

**TODOs:**
```
src/app/io/mod.spl:
- [ ] Use pure-Simple LLVM path when compiler modules work in interpreter
- [ ] Import BaremetalBuilder directly
- [ ] Import compiler.driver and compiler.backend.llvm_backend

src/compiler/baremetal/link_wrapper.spl:
- [ ] Use rt_cli_get_args()
- [ ] Use rt_exit()
```

**Implementation steps:**
1. Fix runtime limitations blocking compiler modules
2. Add missing FFI functions
3. Enable direct imports
4. Test compilation pipeline
5. Delete TODOs

---

## Phase 3: Re-enable Commented Code (~30 items)

**Timeline:** Month 3-4 (Apr-May 2026)
**Priority:** P2 - Features waiting for dependencies

### 3.1 Collection Modules (10 TODOs)

**Files affected:**
- `src/app/interpreter/core/environment.spl`
- `src/app/interpreter/core/eval.spl`
- `src/app/interpreter/collections/persistent_dict.spl`

**TODOs:**
```
- [ ] Re-enable when collections module is complete
- [ ] Re-enable when Lazy and PersistentDict are complete
- [ ] Remove workarounds once static method calls work in interpreter
```

**Implementation steps:**
1. Complete collection module implementations
2. Fix static method call support in interpreter
3. Re-enable commented code
4. Test interpreter
5. Delete TODOs

---

### 3.2 AST Construction (5 TODOs)

**TODOs:**
```
src/app/interpreter/helpers/macros.spl:
- [ ] Re-enable when AST construction syntax is fixed
```

**Implementation steps:**
1. Fix AST construction in runtime parser
2. Re-enable macro code
3. Test macros
4. Delete TODOs

---

### 3.3 Runtime Features (15 TODOs)

**TODOs:**
```
src/app/interpreter/expr/__init__.spl:
- [ ] Re-enable when RuntimeValue.Tensor variant is added

src/compiler/backend.spl:
- [ ] Re-enable backends when parse errors fixed
```

**Implementation steps:**
1. Add missing runtime variants
2. Fix parse errors
3. Re-enable code
4. Test features
5. Delete TODOs

---

## Phase 4: Language Runtime Limitations (~20 items)

**Timeline:** Month 4-5 (May-Jun 2026)
**Priority:** P2 - Requires runtime improvements

### 4.1 Generic Type Support

**Issue:** Generics don't work in runtime parser

**Affected areas:**
- Template instantiation
- Generic collections
- Type parameters

**Implementation steps:**
1. Fix runtime parser to support `<>` syntax
2. Add generic type representation
3. Test generic code in interpreter
4. Remove limitation notes
5. Delete TODOs

---

### 4.2 Static Method Calls

**Issue:** Static method calls fail in interpreter

**TODOs:**
```
src/app/interpreter/collections/persistent_dict.spl:
- [ ] Remove workarounds once static method calls supported
```

**Implementation steps:**
1. Fix interpreter to handle static methods
2. Remove workarounds
3. Test static calls
4. Delete TODOs

---

### 4.3 Multi-line Expressions

**Issue:** Multi-line boolean expressions cause parse errors

**Implementation steps:**
1. Fix runtime parser line handling
2. Test multi-line expressions
3. Remove single-line workarounds
4. Delete TODOs

---

## Phase 5: General TODOs (~606 items)

**Timeline:** Month 5-8 (Jun-Sep 2026)
**Priority:** P3 - Incremental improvements

### 5.1 Optimization Stubs (30 TODOs)

**Files affected:**
- `src/compiler/mir_opt/*.spl`

**TODOs:**
```
src/compiler/mir_opt/inline.spl:
- [ ] Implement actual inlining logic
- [ ] Implement full module-level inlining

src/compiler/mir_opt/loop_opt.spl:
- [ ] Implement iteration count analysis
- [ ] Implement full LICM algorithm
- [ ] Implement loop unrolling
- [ ] Implement strength reduction patterns
```

**Strategy:** Low priority, implement as needed for performance

---

### 5.2 Feature Enhancements (576 TODOs)

**Distribution:** Scattered across all modules

**Strategy:**
1. Categorize by impact (user-facing vs internal)
2. Group by feature area
3. Implement highest-impact first
4. Clean up as features are completed

**Implementation:** Ongoing, opportunistic

---

## Automated TODO Management

### Track with Tool

```bash
# Scan TODOs
bin/simple todo-scan

# View by priority
cat doc/TODO.md

# View by area
# ... categorization needed
```

### Cleanup Script

```bash
#!/bin/bash
# After fixing a TODO

FILE=$1
LINE=$2

# Remove TODO line
sed -i "${LINE}d" "$FILE"

# Run tests
bin/simple test

if [ $? -eq 0 ]; then
    jj describe -m "fix: Implement TODO at $FILE:$LINE"
    echo "✅ TODO fixed and committed"
else
    echo "❌ Tests failed. Fix before committing."
    exit 1
fi
```

---

## Prioritization Criteria

### P0 (Critical)
- Blocks major features (SMF loader, linking)
- Prevents compilation
- Affects all users

### P1 (High)
- Platform-specific features
- Performance critical
- Affects some users

### P2 (Medium)
- Code quality improvements
- Feature completeness
- Affects advanced use cases

### P3 (Low)
- Nice-to-have enhancements
- Internal optimizations
- Documentation

---

## Success Metrics

**Phase 1 Success:**
- SMF loader fully functional
- Backends re-enabled
- Native compilation works end-to-end

**Phase 2 Success:**
- All critical FFI functions implemented
- Platform-specific features work
- No missing runtime functions

**Phase 3 Success:**
- All commented code re-enabled
- No workarounds remaining
- Feature parity achieved

**Phase 4 Success:**
- Runtime parser fully capable
- No language limitations documented
- All features work in interpreter

**Phase 5 Success:**
- TODO count < 50
- All high-impact TODOs resolved
- Only optimization TODOs remain

**Final Success:**
- Zero TODOs remaining
- All features implemented
- Clean codebase

---

## Notes

- **Track progress** in doc/TODO.md
- **Test before deleting** TODO comments
- **Group related TODOs** for batch fixing
- **Update this document** as phases complete
- **Commit frequently** with descriptive messages

---

## Next Actions

1. Categorize all 806 TODOs by area
2. Create tracking issues for Phase 1 items
3. Design SMF format if not exists
4. Start implementing SMF loader
5. Update this document with progress

**Start Date:** 2026-02-13
**Target Completion:** 2026-09-30 (8 months)
**Current Phase:** Planning
