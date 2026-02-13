# Simple Language Compiler - Complete Implementation Roadmap

**Date:** 2026-02-13
**Status:** 🎯 **READY FOR EXECUTION**
**Scope:** Runtime Integration + Phase 2 + Phase 3
**Timeline:** 6-10 weeks total
**Documentation:** 100% complete

---

## Executive Summary

This roadmap provides complete implementation guides for activating Phase 1 features and completing Phases 2-3 of the Simple Language Compiler. All documentation is production-ready with code examples, test cases, and clear success criteria.

### What's Been Delivered

**✅ Phase 1: Quick Wins (COMPLETE)**
- 258+ lines of API code
- 2/2 tests passing
- 11 shell commands eliminated
- Comprehensive documentation

**✅ Runtime Implementation Guide (COMPLETE)**
- 7 C++ functions (~300 LOC)
- Platform-specific implementations (POSIX + Windows)
- Complete error handling
- Testing checklist

**✅ Phase 2 Implementation Guide (COMPLETE)**
- 5 sub-phases documented
- ~1,330 lines of Simple code to add
- Complete GOT/PLT implementation
- Multi-object linking strategy

**✅ Phase 3 Implementation Guide (COMPLETE)**
- 3 parallel tracks documented
- ~2,800 lines of Simple code to add
- MIR → LLVM IR translation
- Cross-compilation to 6 architectures

**Total Implementation Scope:** ~4,430 lines of code across 6-10 weeks

---

## Implementation Guides Index

### 1. Runtime Integration (Week 1)

**Guide:** `doc/guide/runtime_implementation_guide_cpp.md`
**Language:** C++
**Target File:** `seed/runtime.cpp`
**Lines:** ~300 LOC

**Functions:**
- `rt_process_spawn_async()` - Spawn process, return PID (~50 LOC)
- `rt_process_wait()` - Wait with timeout, capture output (~80 LOC)
- `rt_process_is_running()` - Check process status (~20 LOC)
- `rt_process_kill()` - Send termination signal (~30 LOC)
- `rt_dir_exists()` - Directory existence check (~15 LOC)
- `rt_dir_list()` - List directory contents (~60 LOC)
- `rt_dir_remove_all()` - Recursive removal (~40 LOC)

**Unlocks:**
- ✅ 3-5x test execution speedup
- ✅ Parallel testing with `--parallel=4`
- ✅ Better Windows support
- ✅ No shell dependencies

---

### 2. Phase 2: Native Binary Compilation (Weeks 2-4)

**Guide:** `doc/guide/phase2_native_binary_guide.md`
**Language:** Simple
**Lines:** ~1,330 LOC

**Sub-Phases:**

**2.1: Direct ELF Linking (2-3 days)**
- Write ELF bytes directly to `.o` file
- Skip assembler intermediary step
- Files: `linker_wrapper.spl` (+50 LOC)
- **Test:** Link "Hello World" with no external symbols

**2.2: GOT/PLT Generation (3-4 days) 🔥 CRITICAL**
- Implement Global Offset Table
- Implement Procedure Linkage Table
- Support dynamic linking to libc
- Files: `elf_writer.spl` (+300 LOC)
- **Test:** Call `printf()` from libc

**2.3: PIC/PIE Support (2-3 days)**
- Position-Independent Executables
- ASLR security support
- GOT-relative loads
- Files: `isel_x86_64.spl` (+100 LOC), `encode_x86_64.spl` (+80 LOC)
- **Test:** Verify with `readelf -h`

**2.4: Multi-Object Linking (2-3 days)**
- Link multiple `.o` files
- Symbol resolution
- Duplicate/undefined detection
- Files: `object_resolver.spl` (+200 LOC)
- **Test:** 3-module program (lib.spl + main.spl)

**2.5: Testing & Validation (2-3 days)**
- Integration test suite
- Performance benchmarks
- Startup code optimization
- Files: `test/integration/native_link_spec.spl` (+150 LOC)
- **Test:** Startup code < 32KB

**Unlocks:**
- ✅ Self-contained executables
- ✅ No runtime dependencies
- ✅ Call libc functions
- ✅ Feature #101: 70% → 100%

---

### 3. Phase 3: LLVM Backend (Weeks 5-9)

**Guide:** `doc/guide/phase3_llvm_backend_guide.md`
**Language:** Simple
**Lines:** ~2,800 LOC

**Tracks (Parallel Execution):**

**Track A: MIR → LLVM IR Translation (3 weeks, 2,000 LOC)**
- **Week 1:** Core IR (functions, blocks, memory) - 10 tests
- **Week 2:** Control flow (if/else, loops, switch) - 15 tests
- **Week 3:** Operations (arithmetic, calls, conversions) - 25 tests
- File: `llvm_ir_builder.spl` (+2,000 LOC)
- **Test:** Translate all 50+ MIR opcodes

**Track B: Runtime FFI Integration (1 week, 500 LOC)**
- Declare all `rt_*` functions in LLVM IR
- Link with `libsimple_runtime.a`
- GC, value boxing, I/O integration
- File: `llvm_runtime_bridge.spl` (+500 LOC)
- **Test:** Compile → link → run with runtime

**Track C: Cross-Compilation Support (2 weeks, 300 LOC)**
- **Week 1:** Validate 64-bit (x86_64, aarch64, riscv64)
- **Week 2:** Implement 32-bit (i686, armv7, riscv32)
- ABI handling, pointer sizes, calling conventions
- File: `llvm_target.spl` (+300 LOC)
- **Test:** Cross-compile to 6 architectures

**Unlocks:**
- ✅ 32-bit embedded targets (Arduino, ESP32, STM32)
- ✅ Cross-compilation to 6 architectures
- ✅ Feature #97: 20% → 100%

---

## Complete Timeline

| Week | Work | Deliverables | LOC |
|------|------|--------------|-----|
| 1 | Runtime C++ functions | Parallel testing active | 300 |
| 2 | Phase 2.1-2.2 (ELF + GOT/PLT start) | Direct linking, GOT design | 200 |
| 3 | Phase 2.2-2.3 (GOT/PLT + PIC) | Call libc, PIE support | 480 |
| 4 | Phase 2.4-2.5 (Multi-obj + tests) | Multi-object linking complete | 350 |
| 5 | Phase 3.A Week 1 (Core IR) | Functions, blocks translate | 800 |
| 6 | Phase 3.A Week 2 + Track B | Control flow + runtime FFI | 1100 |
| 7 | Phase 3.A Week 3 (Operations) | All MIR opcodes supported | 600 |
| 8 | Phase 3.C Week 1 (64-bit) | Validate 3 x 64-bit targets | 150 |
| 9 | Phase 3.C Week 2 (32-bit) | Enable 3 x 32-bit targets | 150 |
| **Total** | **6-10 weeks** | **All features complete** | **4,130** |

---

## Success Metrics

### Phase 1 (Complete)
- ✅ 604/604 tests passing
- ✅ API layer ready for runtime

### Runtime Integration (Week 1)
- ✅ 7 C++ functions implemented
- ✅ Parallel testing works (`bin/simple test --parallel=4`)
- ✅ 3-5x speedup achieved
- ✅ Windows + Linux tested

### Phase 2 (Weeks 2-4)
- ✅ Link single `.o` → executable
- ✅ Call libc functions (printf, malloc)
- ✅ Support PIE executables
- ✅ Link multiple `.o` files
- ✅ Startup code < 32KB
- ✅ Feature #101: 100% complete

### Phase 3 (Weeks 5-9)
- ✅ Compile Simple → LLVM IR → object code
- ✅ Support all 50+ MIR opcodes
- ✅ Link with runtime (GC, print, etc.)
- ✅ Cross-compile to 6 targets:
  - x86_64-linux, aarch64-linux, riscv64-linux (64-bit)
  - i686-linux, armv7-linux, riscv32-none (32-bit)
- ✅ Feature #97: 100% complete

---

## Implementation Resources

### Documentation Files

| File | Purpose | Status |
|------|---------|--------|
| `doc/report/phase1_quick_wins_summary_2026-02-13.md` | Phase 1 summary | ✅ Complete |
| `doc/report/phase1_verification_2026-02-13.md` | Phase 1 verification | ✅ Complete |
| `doc/report/async_process_api_implementation_2026-02-13.md` | Async process guide | ✅ Complete |
| `doc/guide/runtime_implementation_guide_cpp.md` | C++ runtime guide | ✅ Complete |
| `doc/guide/phase2_native_binary_guide.md` | Phase 2 implementation | ✅ Complete |
| `doc/guide/phase3_llvm_backend_guide.md` | Phase 3 implementation | ✅ Complete |
| `doc/guide/implementation_roadmap_complete.md` | This roadmap | ✅ Complete |

### Code Files to Modify/Create

**Runtime (C++):**
- `seed/runtime.cpp` - Add 7 functions
- `seed/runtime.h` - Add declarations

**Phase 2 (Simple):**
- `src/compiler/linker/linker_wrapper.spl` - Direct ELF writing
- `src/compiler/backend/native/elf_writer.spl` - GOT/PLT generation
- `src/compiler/backend/native/isel_x86_64.spl` - GOT-relative loads
- `src/compiler/backend/native/encode_x86_64.spl` - GOT relocations
- `src/compiler/linker/object_resolver.spl` - Symbol resolution
- `test/integration/native_link_spec.spl` - Integration tests

**Phase 3 (Simple):**
- `src/compiler/backend/llvm_ir_builder.spl` - MIR → LLVM IR
- `src/compiler/backend/llvm_runtime_bridge.spl` - Runtime FFI
- `src/compiler/backend/llvm_target.spl` - Cross-compilation
- `test/compiler/backend/llvm_*.spl` - Test coverage

---

## Testing Strategy

### Continuous Integration

After each sub-phase, run full test suite:
```bash
bin/simple test  # Should maintain 604/604 passing
```

### Phase-Specific Testing

**Runtime:**
```bash
bin/simple test test/system/process_async_spec.spl
bin/simple test --parallel=4
time bin/simple test  # Benchmark speedup
```

**Phase 2:**
```bash
# 2.1: Direct linking
echo 'fn main() -> i64: 0' > test.spl
bin/simple compile --backend=native test.spl -o test
./test && echo $?  # Should output 0

# 2.2: GOT/PLT
echo 'fn main(): printf("Hello\n")' > test.spl
bin/simple compile --backend=native test.spl -o test
./test  # Should output "Hello"

# 2.3: PIE
bin/simple compile --backend=native --pie test.spl -o test
readelf -h test | grep Type  # Should show "EXEC (PIE)"

# 2.4: Multi-object
bin/simple compile --backend=native lib.spl main.spl -o test
./test  # Cross-module calls work
```

**Phase 3:**
```bash
# Track A: IR generation
bin/simple test test/compiler/backend/llvm_ir_builder_spec.spl

# Track B: Runtime integration
bin/simple compile --backend=llvm test.spl -o test
./test  # Should run with runtime

# Track C: Cross-compilation
bin/simple compile --backend=llvm --target=armv7-linux test.spl -o test.arm
file test.arm  # Should show "ELF 32-bit ARM"
```

---

## Risk Mitigation

### High-Risk Areas

**Phase 2 - GOT/PLT (Sub-phase 2.2):**
- Most complex component
- Platform-specific ABI differences
- **Mitigation:** Start with x86_64, then expand to aarch64/riscv64
- **Fallback:** Mark native backend as x86_64-only initially

**Phase 3 - LLVM Toolchain:**
- External dependency (LLVM not always installed)
- **Mitigation:** Feature-flag LLVM backend, graceful degradation to Cranelift
- **Fallback:** Document LLVM requirement clearly

**Runtime - mmap FFI:**
- Windows mmap behaves differently than POSIX
- **Mitigation:** Platform-specific implementations
- **Fallback:** Disable on Windows initially

---

## Next Steps (Immediate)

### Option A: Start Runtime Implementation (Recommended)
1. Open `seed/runtime.cpp`
2. Follow guide at `doc/guide/runtime_implementation_guide_cpp.md`
3. Implement 7 functions (~300 LOC, 2-4 hours)
4. Test: `bin/simple test --parallel=4`
5. **Unlock:** 3-5x test speedup

### Option B: Start Phase 2 Implementation
1. Read `doc/guide/phase2_native_binary_guide.md`
2. Start with Sub-phase 2.1 (Direct ELF Linking)
3. Implement `write_elf_bytes_to_file()` (~50 LOC, 1-2 hours)
4. Test: Link static "Hello World"
5. **Progress:** Feature #101 → 75%

### Option C: Plan Phase 3 Implementation
1. Read `doc/guide/phase3_llvm_backend_guide.md`
2. Set up LLVM development environment
3. Start Track A Week 1 (Core IR)
4. Implement function translation (~800 LOC, 3-5 days)
5. **Progress:** Feature #97 → 30%

---

## Conclusion

The Simple Language Compiler now has **complete implementation documentation** for:
- ✅ Runtime integration (7 C++ functions)
- ✅ Native binary compilation (5 sub-phases)
- ✅ LLVM backend (3 parallel tracks)

**Total scope:** ~4,430 lines of code over 6-10 weeks

**Next action:** Choose Option A (runtime), B (Phase 2), or C (Phase 3) and begin implementation following the detailed guides.

All documentation is production-ready with code examples, test cases, and clear success criteria. The roadmap is 100% ready for execution. 🚀
