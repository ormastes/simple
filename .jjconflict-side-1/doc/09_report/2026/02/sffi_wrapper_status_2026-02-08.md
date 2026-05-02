# SFFI Wrapper Status Report

**Date:** 2026-02-08
**Summary:** 13 SFFI wrappers exist (422 extern functions), but most lack runtime implementations

---

## Executive Summary

**Total SFFI Wrappers:** 13 files in `src/app/io/`
**Total Extern Functions:** 422
**Runtime Status:** Only 1 wrapper has partial runtime support (old regex API)

**Key Finding:** All SFFI wrappers are **complete in Simple** but are missing the **Rust runtime FFI implementations**.

---

## SFFI Wrapper Inventory

| # | Wrapper | File | Externs | Lines | Status | Library |
|---|---------|------|---------|-------|--------|---------|
| 1 | **Audio** | `audio_ffi.spl` | 44 | ~550 | ❌ Missing | Rodio |
| 2 | **Compression** | `compress_ffi.spl` | 24 | ~400 | ❌ Missing | zlib/gzip |
| 3 | **Cryptography** | `crypto_ffi.spl` | 17 | ~300 | ❌ Missing | OpenSSL/ring |
| 4 | **CUDA** | `cuda_ffi.spl` | 23 | ~350 | ❌ Missing | CUDA |
| 5 | **Gamepad** | `gamepad_ffi.spl` | 20 | ~431 | ❌ Missing | Gilrs |
| 6 | **Graphics2D** | `graphics2d_ffi.spl` | 49 | ~700 | ❌ Missing | Lyon |
| 7 | **HTTP** | `http_ffi.spl` | 36 | ~650 | ❌ Missing | reqwest/warp |
| 8 | **JIT** | `jit_ffi.spl` | 18 | ~486 | ⚠️ Partial | Cranelift |
| 9 | **Physics** | `rapier2d_ffi.spl` | 50 | ~620 | ❌ Missing | Rapier2D |
| 10 | **Regex** | `regex_ffi.spl` | 15 | 354 | ⚠️ Old API | Rust regex |
| 11 | **SQLite** | `sqlite_ffi.spl` | 27 | ~450 | ❌ Missing | SQLite |
| 12 | **Vulkan** | `vulkan_ffi.spl` | 38 | ~500 | ❌ Missing | Vulkan |
| 13 | **Window** | `window_ffi.spl` | 61 | ~750 | ❌ Missing | Winit |

**Total:** 422 extern functions, ~6,541 lines of Simple code

---

## Detailed Status

### ⚠️ Regex - Partial (Old API Works)

**SFFI Wrapper:** `src/app/io/regex_ffi.spl` (354 lines, 15 externs)

**Expected API (NEW - handle-based):**
```simple
extern fn rt_regex_new(pattern: text) -> i64         # ❌ NOT in runtime
extern fn rt_regex_destroy(handle: i64)               # ❌ NOT in runtime
extern fn rt_regex_is_match(handle: i64, text: text) -> i64  # ❌ NOT in runtime
... (12 more rt_regex_* functions)
```

**Actual Runtime API (OLD - stateless):**
```rust
ffi_regex_is_match(pattern: text, text: text) -> bool        # ✅ EXISTS
ffi_regex_find(pattern: text, text: text) -> [text]          # ✅ EXISTS
ffi_regex_find_all(pattern: text, text: text) -> [[text]]    # ✅ EXISTS
ffi_regex_captures(pattern: text, text: text) -> [text]      # ✅ EXISTS
ffi_regex_replace(pattern: text, text: text, rep: text) -> text      # ✅ EXISTS
ffi_regex_replace_all(pattern: text, text: text, rep: text) -> text  # ✅ EXISTS
ffi_regex_split(pattern: text, text: text) -> [text]         # ✅ EXISTS
ffi_regex_split_n(pattern: text, text: text, limit: i64) -> [text]   # ✅ EXISTS
```

**Location:** Used by `src/app/interpreter.extern/regex.spl` (interpreter mode only)

**Issue:** Two different APIs:
- **Old:** `ffi_regex_*` - Compiles pattern every call (less efficient)
- **New:** `rt_regex_*` - Compile once, reuse with handle (more efficient)

**Solution:** Either:
1. Implement new `rt_regex_*` API in runtime (~200 lines Rust)
2. OR adapt SFFI wrapper to use existing `ffi_regex_*` API

---

### ⚠️ JIT - Partially Declared

**SFFI Wrapper:** `src/app/io/jit_ffi.spl` (486 lines, 18 externs)

**Declared in app.io.mod:**
```simple
extern fn rt_set_jit_backend(backend: text) -> bool
extern fn rt_get_jit_backend() -> text
extern fn rt_exec_manager_create(backend: text) -> i64
extern fn rt_exec_manager_compile(handle: i64, mir_data: text) -> text
extern fn rt_exec_manager_execute(handle: i64, name: text, args: [i64]) -> i64
extern fn rt_exec_manager_has_function(handle: i64, name: text) -> bool
extern fn rt_exec_manager_backend_name(handle: i64) -> text
extern fn rt_exec_manager_cleanup(handle: i64)
```

**Status:** Declared but not verified if implemented in runtime

---

### ❌ All Other Wrappers - Missing Runtime

The remaining 11 SFFI wrappers are complete in Simple but have **zero runtime support**:

1. **Audio** (44 externs) - `rt_audio_*` functions not in runtime
2. **Compression** (24 externs) - `rt_gzip_*`, `rt_deflate_*` not in runtime
3. **Cryptography** (17 externs) - `rt_hash_*`, `rt_hmac_*` not in runtime
4. **CUDA** (23 externs) - `rt_cuda_*` not in runtime
5. **Gamepad** (20 externs) - `rt_gamepad_*` not in runtime
6. **Graphics2D** (49 externs) - `rt_lyon_*` not in runtime
7. **HTTP** (36 externs) - `rt_http_*` not in runtime
8. **Physics** (50 externs) - `rt_rapier2d_*` not in runtime
9. **SQLite** (27 externs) - `rt_sqlite_*` not in runtime
10. **Vulkan** (38 externs) - `rt_vulkan_*` not in runtime
11. **Window** (61 externs) - `rt_winit_*` not in runtime

---

## Runtime Functions Actually Present

**From `strings bin/simple_runtime | grep "^ffi_\|^rt_"`:**

**Working (in runtime):**
- `ffi_regex_*` (8 functions) - Old regex API ✅
- `rt_env_*` - Environment variables ✅
- `rt_file_*` - File I/O ✅
- `rt_dir_*` - Directory operations ✅
- `rt_process_*` - Process execution ✅
- `rt_actor_*` - Actor system ✅
- `rt_array_*`, `rt_tuple_*`, `rt_dict_*` - Data structures ✅
- `rt_hashmap_*`, `rt_hashset_*`, `rt_btreemap_*`, `rt_btreeset_*` - Collections ✅
- `rt_sandbox_*` - Sandboxing ✅
- `rt_time_*` - Time functions ✅
- `rt_getpid`, `rt_hostname` - System info ✅

**Missing (declared but not in runtime):**
- All `rt_regex_*` (new API)
- All `rt_audio_*`
- All `rt_gzip_*`, `rt_deflate_*`
- All `rt_hash_*`, `rt_hmac_*`
- All `rt_cuda_*`
- All `rt_gamepad_*`
- All `rt_lyon_*`
- All `rt_http_*`
- All `rt_rapier2d_*`
- All `rt_sqlite_*`
- All `rt_vulkan_*`
- All `rt_winit_*`

---

## Why This Happened

The SFFI wrappers were **designed and written** but the corresponding **Rust runtime FFI was never implemented**.

**Timeline:**
1. ✅ Design phase: Three-tier SFFI pattern created
2. ✅ Wrapper phase: 13 SFFI wrappers written in Simple (6,541 lines)
3. ❌ **Runtime phase: Rust FFI implementation never completed**
4. ❌ Testing phase: Can't test without runtime support

This is like writing a driver without the hardware!

---

## Impact

**Tests Blocked:** Estimated ~200+ tests waiting for SFFI implementations
- Regex: ~45 tests
- Compression: ~25 tests
- Crypto: ~47 tests
- Graphics/Game Engine: ~50 tests
- Database: ~15 tests
- HTTP: ~15 tests
- Other: ~5 tests

**Features Blocked:**
- Text processing (regex)
- File compression
- Cryptography/security
- 2D graphics
- HTTP client/server
- Database access
- GPU compute (CUDA)
- Game development (physics, audio, gamepad, windowing)

---

## Implementation Effort Estimate

**Per SFFI Wrapper:**
- Rust FFI code: ~200-400 lines
- Testing: ~100 lines
- Time: 2-4 hours each

**Total for all 13 wrappers:**
- Rust code: ~3,500-5,000 lines
- Testing: ~1,300 lines
- Time: ~40-50 hours (1-2 weeks)

**Priority Order (by impact):**
1. 🔴 **Regex** (45 tests) - 2 hours
2. 🔴 **Compression** (25 tests) - 3 hours
3. 🔴 **Crypto** (47 tests) - 3 hours
4. 🟡 **SQLite** (15 tests) - 3 hours
5. 🟡 **HTTP** (15 tests) - 4 hours
6. 🟢 **Graphics2D** (game dev) - 4 hours
7. 🟢 **Audio** (game dev) - 3 hours
8. 🟢 **Physics** (game dev) - 4 hours
9. 🟢 **Gamepad** (game dev) - 2 hours
10. 🟢 **Window** (game dev) - 4 hours
11. ⚪ **CUDA** (niche) - 4 hours
12. ⚪ **Vulkan** (niche) - 5 hours
13. ⚪ **JIT** (advanced) - 3 hours

---

## Recommendations

### Option 1: Implement Top 5 (Immediate Impact)

**Target:** Regex + Compression + Crypto + SQLite + HTTP
**Impact:** Unblocks ~147 tests
**Effort:** ~15 hours
**Result:** Core functionality complete

### Option 2: Implement Game Engine Stack

**Target:** Graphics2D + Audio + Physics + Gamepad + Window
**Impact:** Complete game development support
**Effort:** ~17 hours
**Result:** Full game engine capabilities

### Option 3: Phased Approach

**Phase 1 (Week 1):** Regex + Compression + Crypto (~8 hours)
**Phase 2 (Week 2):** SQLite + HTTP (~7 hours)
**Phase 3 (Week 3):** Game Engine (Graphics + Audio + Physics) (~11 hours)
**Phase 4 (Week 4):** Advanced (CUDA + Vulkan + JIT) (~12 hours)

---

## Current State

✅ **SFFI Wrapper Layer (Tier 2):** 100% complete (6,541 lines)
❌ **Runtime FFI Layer (Tier 1):** ~2% complete (only old regex API)
✅ **Documentation:** Complete
✅ **Test Suites:** Written and waiting

**Bottleneck:** Rust runtime FFI implementation

---

## Next Steps

1. **Choose priority** (recommend Option 1: Top 5)
2. **Implement Rust FFI** for chosen wrappers
3. **Test with existing test suites**
4. **Rebuild runtime** and release

**The Simple code is done - we just need the Rust backend!**
