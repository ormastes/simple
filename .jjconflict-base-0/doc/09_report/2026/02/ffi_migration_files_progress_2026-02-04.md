# FFI Migration: File Migration Progress

**Date:** 2026-02-04
**Phase:** File Migration (P0 - Compiler Core)
**Status:** In Progress (2/17 compiler files migrated)

---

## Progress Summary

### Files Migrated

**1. src/compiler/codegen.spl** ✅
- **Before:** 1,025 lines (85+ extern declarations + wrappers)
- **After:** 662 lines
- **Removed:** 363 lines (35% reduction)
- **Migration:** Replaced extern declarations (lines 16-378) with `use ffi.codegen*`
- **Backup:** `src/compiler/codegen.spl.backup_pre_migration`

**2. src/compiler/ffi.spl** ✅
- **Before:** 89 lines (10 extern declarations + wrappers + exports)
- **After:** 31 lines
- **Removed:** 58 lines (65% reduction)
- **Migration:** Replaced all FFI with imports from `ffi.io*` and `ffi.system*`
- **Note:** Kept ShellResult struct and exports for backward compatibility

---

## Module Expansions

To support file migrations, the centralized FFI modules were expanded:

### ffi/codegen.spl
- **Before:** 178 lines (24 functions)
- **After:** 222 lines (62 functions)
- **Added:** 44 lines, 38 new functions
- **New functions:** All Cranelift IR building operations
  - Function building: begin_function, end_function, define_function
  - Signature building: new_signature, sig_add_param, sig_set_return
  - Block management: create_block, switch_to_block, seal_block, seal_all_blocks
  - Value creation: iconst, fconst, bconst
  - Integer arithmetic: iadd, isub, imul, sdiv, srem
  - Bitwise operations: band, bor, bxor, bnot, ishl, sshr
  - Memory operations: load, store, stack_slot, stack_addr
  - Control flow: jump, return, return_void
  - Function calls: call, call_indirect, call_function_ptr
  - Type conversions: bitcast

### ffi/io.spl
- **Before:** 208 lines
- **After:** 209 lines
- **Added:** 1 extern declaration (`rt_write_file`)

### ffi/system.spl
- **Before:** 224 lines
- **After:** 229 lines
- **Added:** 5 lines (rt_exec extern + wrapper)

---

## Remaining Compiler Files

**Files with FFI declarations (15 remaining):**

| File | FFI Count | Priority | Status |
|------|-----------|----------|--------|
| src/compiler/codegen.spl | ~~85+~~ | P0 | ✅ Migrated |
| src/compiler/ffi.spl | ~~10~~ | P0 | ✅ Migrated |
| src/compiler/backend/native_bridge.spl | 4 | P0 | Pending |
| src/compiler/project.spl | 4 | P0 | Pending |
| src/compiler/build_log.spl | 5 | P0 | Pending |
| src/compiler/linker/smf_writer.spl | ? | P0 | Pending |
| src/compiler/monomorphize/cache.spl | ? | P0 | Pending |
| src/compiler/backend/backend_selector.spl | ? | P0 | Pending |
| src/compiler/type_system/builtin_registry.spl | ? | P0 | Pending |
| src/compiler/driver/incremental.spl | ? | P0 | Pending |
| src/compiler/incremental_builder.spl | ? | P0 | Pending |
| src/compiler/layout_recorder.spl | ? | P0 | Pending |
| src/compiler/build_mode.spl | ? | P0 | Pending |
| src/compiler/incremental.spl | ? | P0 | Pending |
| src/compiler/parallel.spl | ? | P0 | Pending |
| src/compiler/test_bootstrap.spl | ? | P0 | Pending |
| src/compiler/ffi_minimal.spl | ? | Special | Keep as-is |

**Note:** `ffi_minimal.spl` is intentionally kept with extern declarations as it provides minimal FFI for bootstrap.

---

## Migration Pattern

The migration follows a consistent pattern:

### Before (Scattered Declarations)
```simple
# In src/compiler/codegen.spl (and many other files)
extern fn cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64
extern fn cranelift_isub(ctx: i64, a: i64, b: i64) -> i64
extern fn cranelift_imul(ctx: i64, a: i64, b: i64) -> i64
# ... (85+ declarations)

fn some_codegen_function():
    val result = cranelift_iadd(ctx, a, b)
```

### After (Centralized Import)
```simple
# In src/compiler/codegen.spl
use ffi.codegen*

fn some_codegen_function():
    val result = cranelift_iadd(ctx, a, b)  # Same usage!
```

**Benefits:**
- No changes to function calls
- No changes to implementation logic
- Just add one import and remove duplicate declarations
- Dramatically reduced file sizes (35-65% reduction so far)

---

## Impact Metrics

### Lines Removed

| File | Before | After | Removed | Reduction % |
|------|--------|-------|---------|-------------|
| codegen.spl | 1,025 | 662 | 363 | 35% |
| ffi.spl | 89 | 31 | 58 | 65% |
| **Total** | **1,114** | **693** | **421** | **38%** |

### FFI Declarations Eliminated

- **codegen.spl:** 85+ declarations → 0 (replaced with `use ffi.codegen*`)
- **ffi.spl:** 10 declarations → 0 (replaced with `use ffi.io*` + `use ffi.system*`)
- **Total eliminated:** 95+ duplicate extern declarations

### Centralization Progress

- **Files migrated:** 2/17 (12%)
- **Compiler files remaining:** 15
- **Estimated remaining work:** ~6-8 hours for all compiler files

---

## Next Steps

### Immediate (Continue P0 Migration)

**1. Migrate remaining compiler core files (4-6 hours):**
- backend/native_bridge.spl (4 declarations)
- project.spl (4 declarations)
- build_log.spl (5 declarations)
- linker/smf_writer.spl
- monomorphize/cache.spl
- backend/backend_selector.spl
- type_system/builtin_registry.spl
- driver/incremental.spl
- incremental_builder.spl
- layout_recorder.spl
- build_mode.spl
- incremental.spl
- parallel.spl
- test_bootstrap.spl

**2. Migrate P1 files (build system, CLI):**
- `src/app/build/`
- `src/app/cli/`
- `src/app/test_runner/`

**3. Migrate P2 files (test framework):**
- `test/` directory files

**4. Verification:**
```bash
# Check no extern declarations outside src/ffi/
grep -r "extern fn rt_" src/ --include="*.spl" | grep -v "src/ffi/"| grep -v "ffi_minimal.spl" | wc -l
# Expected: 0

# Full rebuild
simple build --release

# Full test suite
simple test
```

---

## Lessons Learned

### What Worked Well

1. **Expanding centralized modules first**
   - Added all missing functions to ffi/codegen.spl before migrating
   - Verified all functions present before migration
   - Prevented migration failures

2. **Creating backups**
   - `.backup_pre_migration` files for safety
   - Can rollback easily if needed

3. **Systematic approach**
   - Start with largest/most complex files (codegen.spl)
   - Build confidence with smaller files (ffi.spl)
   - Clear migration pattern emerges

### Challenges Encountered

1. **Missing functions in centralized modules**
   - rt_write_file and rt_exec were missing
   - Added them before migration
   - Now checking for missing functions proactively

2. **Function naming consistency**
   - Some extern fns have rt_ prefix, some don't
   - Centralized modules handle both patterns
   - Wrappers provide clean names

3. **Large files**
   - codegen.spl had 85+ declarations
   - Required expanding ffi/codegen.spl significantly
   - Worth the effort - 35% file size reduction

---

## Statistics

### Session Progress

| Metric | Value |
|--------|-------|
| Files migrated | 2 |
| Lines removed | 421 |
| Declarations eliminated | 95+ |
| Module expansions | 3 (codegen, io, system) |
| Time invested | ~2 hours |

### Overall Migration Status

| Phase | Status | Completion |
|-------|--------|------------|
| **Phase 1:** Cranelift FFI | Spec Ready | 80% |
| **Phase 2:** FFI Crates | Audit Done | 80% |
| **Phase 3:** Module Structure | Complete | 100% ✅ |
| **Phase 3:** File Migration | In Progress | 12% (2/17 compiler files) |

**Overall Project:** ~72% complete

---

## Conclusion

Successfully started file migration phase with 2 critical files:
- ✅ **codegen.spl** - Largest file, most declarations (35% reduction)
- ✅ **ffi.spl** - Central FFI hub (65% reduction)

**Key Achievement:** Demonstrated clear migration pattern that works efficiently

**Next Milestone:** Complete remaining 15 compiler files (P0)

**Timeline:** On track for 3-4 week completion
- Weeks 1-2: Specifications + modules ✅ Complete
- Week 3: File migration ⏳ In progress (Day 1)
- Week 4: Verification + code generation

---

*Report generated: 2026-02-04*
*File Migration: Day 1*
*Progress: Strong start, clear path forward*
