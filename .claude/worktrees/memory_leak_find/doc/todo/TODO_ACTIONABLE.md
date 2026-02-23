# Actionable TODO Items - Prioritized

**Generated:** 2026-02-11
**Total Items:** 269 TODOs, 426 pending tests
**Focus:** Items that can be implemented without hitting runtime limitations

## Status Summary

### ✅ Completed
- Feature #700 - Database SDN table import/export (marked as failed but actually passing)
- Uncovered branches test suite created (test/unit/compiler/uncovered_branches_spec.spl)

### 🚫 Blocked by Runtime Limitations

**Cannot implement until runtime supports:**
- Generics at runtime (110+ items)
- Try/catch/throw (error handling patterns)
- Async/await keywords
- Module closures and capture
- Multi-line boolean expressions
- Chained method calls

**Examples of blocked items:**
- `src/lib/pure/tensor_f64.spl:4` - Generic PureTensor<T>
- `src/lib/src/di.spl:174` - Generic DI container
- All `test/unit/std/async_*.spl` tests - async syntax
- Macro-related tests - macro keyword not supported

## Priority 1: Quick Wins (0-2 hours)

### 1.1 Update Documentation
- [ ] **Update pending_feature.md** - Feature #700 shows as failed but is passing
- [ ] **Regenerate test results** - Current test_result.md shows all zeros
- [ ] **Update TODO.md** - Run `bin/simple todo-scan`

### 1.2 Enable Working Tests
Investigate these pending tests that might actually work:

- [ ] `test/system/runner_spec.spl` - Property testing runner (no obvious blockers)
- [ ] `test/system/shrinking_spec.spl` - Shrinking logic (pure functions)
- [ ] `test/system/generators_spec.spl` - Generator implementations (already has code)

**Action:** Try removing `@pending` and run each test individually.

### 1.3 Add Missing Test Coverage
Based on doc/test/uncovered_branches_analysis.md:

- [x] Type system edge cases (completed)
- [ ] Buffer overflow protection tests
- [ ] Expression depth tracking tests
- [ ] Error recovery path tests

## Priority 2: Simple Implementations (2-8 hours)

### 2.1 String Parsing Functions
**File:** `src/lib/text.spl` or similar

Implement these if missing:
- [ ] `ends_with` edge cases (see uncovered_branches_analysis line 121)
- [ ] String interpolation with nested braces
- [ ] Escaped brace handling

### 2.2 Stub Implementations
Many stubs marked as "TODO: Implement" that could have basic implementations:

**Examples:**
- `src/app/build/baremetal.spl:305` - Add timeout support stubs
- `src/app/build/test.spl:32` - Basic parallel execution structure
- `src/app/build/quality.spl:156` - Parsing stubs

**Approach:** Implement basic versions that return reasonable defaults.

### 2.3 Helper Functions
Look for functions with `TODO: implement` that are:
- Pure functions (no side effects)
- No generics required
- Clear specifications

**Search pattern:** `grep -r "fn.*TODO.*implement" src/`

## Priority 3: Medium Implementations (1-2 days)

### 3.1 FFI Wrapper Stubs
Many FFI wrappers marked as TODO:

- `src/app/wrapper_gen/tier1_cpp.spl:267` - Generate boilerplate
- `src/app/wrapper_gen/tier1_rust_gen.spl:287` - Generate boilerplate
- `src/app/audit/ffi_analyzer.spl:287` - Add wrapper stubs

**Action:** Generate skeleton implementations that can be filled in later.

### 3.2 Test Scaffolding
- `src/app/test/scaffold.spl` - Adds "TODO: Add assertions"
- Could generate better default assertions based on context

### 3.3 Compiler Stubs
Several compiler modules have "TODO: implement" for features that aren't critical:

- `src/compiler/mir_opt/inline.spl:406` - Inlining logic (can be no-op)
- `src/compiler/mir_opt/loop_opt.spl:91` - Loop opts (can be no-op initially)

## Priority 4: Infrastructure (2-5 days)

### 4.1 SMF (Simple Module Format) Implementation
Many TODOs around SMF handling:

- `src/compiler/loader/smf_cache.spl:104` - Proper header parsing
- `src/compiler/linker/smf_reader.spl:233` - Template parsing
- `src/compiler/monomorphize/hot_reload.spl:302` - Section table calculation

**Impact:** High - enables module system improvements

### 4.2 File I/O Operations
Several file operations marked as TODO:

- `src/compiler/monomorphize/hot_reload.spl:352` - file_write_at FFI
- `src/compiler/monomorphize/hot_reload.spl:363` - file_read_at FFI
- `test/app/package/ffi_spec.spl:17` - File write via fs

**Blocker:** Needs FFI support in runtime

### 4.3 Process Management
- `test/unit/std/process_spec.spl` - Skipped, needs rt_process_* functions
- `src/app/test_runner_new/test_runner_parallel.spl:51` - True parallel execution

**Blocker:** Needs rt_process_spawn_async

## Priority 5: Not Actionable (Future Work)

### 5.1 Awaiting Language Features
- Async/await support
- Macro system
- Generic runtime support
- Try/catch/throw

### 5.2 Awaiting External Dependencies
- Lean 4 verification integration
- LLVM backend (Feature #97)
- Native binary compilation (Feature #101)
- GPU/CUDA/Vulkan support

## Recommended Immediate Actions

**This Session:**
1. ✅ Add uncovered branches test (completed)
2. Update doc/feature/pending_feature.md
3. Try enabling 3-5 pending tests to see if they work
4. Run `bin/simple todo-scan` to regenerate TODO.md

**Next Session:**
1. Implement simple string helper functions
2. Add more test coverage for uncovered branches
3. Generate FFI wrapper boilerplate
4. Implement stub/no-op versions of compiler optimizations

**Long Term:**
1. Wait for runtime to support generics
2. Implement SMF handling infrastructure
3. Add FFI support for file/process operations
4. Enable async/await syntax support

## Notes

- Many "pending" tests are actually blocked by runtime limitations, not missing implementations
- Focus on pure functions and test coverage first
- Generate stubs/boilerplate to reduce TODO count
- Document runtime limitations clearly to avoid wasted effort
- Prioritize what can be tested immediately
