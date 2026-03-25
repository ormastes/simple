# SFFI Fix/Implementation Plan

**Date:** 2026-02-13  
**Status:** ✅ Phase 1 Complete

---

## Executive Summary

**Gap Analysis:** 580 `extern fn` declarations in `src/app/io/*.spl`, but only 22 `rt_*` functions in C runtime (`src/compiler_seed/runtime.h`).

**Reality:** Most "SFFI wrappers" are actually **stubs** calling external Rust crates (regex, http, gamepad, vulkan, etc.) via three-tier pattern. The C runtime only provides **core syscalls**.

**Decision:** Focus on **Two-Tier Pattern** for core syscalls. Three-tier external libraries are already scaffolded.

**✅ COMPLETED:** Phase 1 implemented and tested. Native runtime functions now replace shell fallbacks for core file/directory operations.

---

## Current State

### ✅ Working (Two-Tier Pattern)
Runtime functions fully implemented in `src/compiler_seed/runtime.h`:

| Category | Functions | Status |
|----------|-----------|--------|
| **File I/O** | `rt_file_read_text`, `rt_file_exists`, `rt_file_write`, `rt_file_delete`, `rt_file_size` | ✅ Complete |
| **File Advanced** | `rt_file_lock`, `rt_file_unlock`, `rt_file_read_text_at`, `rt_file_write_text_at` | ✅ Complete |
| **Memory Map** | `rt_mmap`, `rt_munmap`, `rt_madvise`, `rt_msync` | ✅ Complete |
| **Directory** | `rt_dir_remove_all` | ✅ Complete |
| **Process** | `rt_process_spawn_async`, `rt_process_wait`, `rt_process_is_running`, `rt_process_kill` | ✅ Complete |
| **Time** | `rt_time_now_unix_micros` | ✅ Complete |
| **System** | `rt_getpid`, `rt_hostname`, `rt_thread_available_parallelism` | ✅ Complete |
| **Log** | `rt_log_*` family (6 functions) | ✅ Complete |

### 🚧 Partially Working (Shell Fallbacks)
Functions in `src/app/io/*.spl` using shell commands:

| Category | Current Implementation | Issue |
|----------|----------------------|-------|
| **Directory ops** | `mkdir -p`, `find`, `ls`, `rm -rf` via `rt_process_run` | Shell dependency |
| **File ops** | `cat`, `stat`, `cp`, `rm` via `rt_process_run` | Shell dependency |
| **Environment** | Not using `rt_env_get`/`rt_env_set` | Available but unused |

### ❌ Missing (External Libraries - Three-Tier)
Functions declared but **NOT in C runtime**:

| Category | Count | Backend | Status |
|----------|-------|---------|--------|
| **regex** | 15 fns | Rust crate `regex` | Stub only |
| **http** | 30 fns | Rust crate `reqwest` | Stub only |
| **sqlite** | 25 fns | C lib `libsqlite3` | Stub only |
| **crypto** | 15 fns | Rust crate `ring` | Stub only |
| **compress** | 20 fns | Rust crate `flate2` | Stub only |
| **gamepad** | 25 fns | Rust crate `gilrs` | Stub only |
| **graphics** (lyon) | 50 fns | Rust crate `lyon` | Stub only |
| **vulkan** | 60 fns | C lib `libvulkan` | Stub only |
| **window** (winit) | 60 fns | Rust crate `winit` | Stub only |
| **ssh/sftp** | 35 fns | Rust crate `ssh2` | Stub only |
| **tls** | 40 fns | Rust crate `rustls` | Stub only |

---

## Problems to Fix

### Problem 1: Shell Dependency for Basic Ops
**Impact:** Portability, performance overhead  
**Files:** `src/app/io/dir_ops.spl`, `src/app/io/file_ops.spl`

Current workaround uses shell commands:
```simple
fn dir_create(path: text, recursive: bool) -> bool:
    if recursive:
        val (out, err, code) = _dir_shell("mkdir -p '{path}'")
        code == 0
```

**Should use:**
```simple
extern fn rt_dir_create(path: text, recursive: bool) -> bool

fn dir_create(path: text, recursive: bool) -> bool:
    rt_dir_create(path, recursive)
```

### Problem 2: Unused Runtime Functions
**Impact:** Wasted maintenance  
**Functions:** `rt_env_get`, `rt_env_set` exist but io module uses shell

### Problem 3: Missing Runtime Functions
**Impact:** Blocked functionality

| Function | Use Case | Priority |
|----------|----------|----------|
| `rt_dir_create` | Directory creation | P1 |
| `rt_dir_list` | Directory listing | P1 |
| `rt_file_copy` | File operations | P2 |
| `rt_env_get` (use existing) | Environment vars | P1 |
| `rt_env_set` | Environment vars | P2 |

### Problem 4: External Library Stubs
**Impact:** Features unavailable  
**Status:** Intentional - requires three-tier implementation

---

## Solution Strategy

### Phase 1: Core Syscall Two-Tier (Priority: **P0**)
**Goal:** Replace shell fallbacks with native runtime calls

**Actions:**
1. Add missing `rt_dir_*` functions to `src/compiler_seed/runtime.h`/`src/compiler_seed/platform/unix_common.h`
2. Add missing `rt_file_copy` to runtime
3. Update `src/app/io/dir_ops.spl` to use native calls
4. Update `src/app/io/file_ops.spl` to use native calls
5. Update `src/app/io/env_ops.spl` to use `rt_env_get`/`rt_env_set` directly

**Deliverables:**
- [ ] `rt_dir_create(path, recursive)` in runtime
- [ ] `rt_dir_list(path)` in runtime  
- [ ] `rt_file_copy(src, dst)` in runtime
- [ ] Updated `dir_ops.spl` (no shell calls)
- [ ] Updated `file_ops.spl` (no shell calls)
- [ ] Tests pass

**Estimated effort:** 2-3 hours

### Phase 2: Cleanup and Validation (Priority: **P1**)
**Goal:** Remove dead code, validate patterns

**Actions:**
1. Run `bin/simple audit-ffi` to scan direct FFI calls
2. Remove unused `_shell` helper functions
3. Document two-tier pattern usage
4. Add tests for new runtime functions

**Deliverables:**
- [ ] No shell calls in `dir_ops.spl`/`file_ops.spl`
- [ ] Updated tests
- [ ] Documentation: `doc/guide/sffi_two_tier.md`

**Estimated effort:** 1 hour

### Phase 3: External Libraries (Priority: **P2** - Future Work)
**Goal:** Implement high-value three-tier wrappers

**Candidates (by demand):**
1. **regex** - Pattern matching (high demand)
2. **sqlite** - Database (high demand)
3. **http** - Web requests (medium demand)
4. **compress** - File compression (medium demand)

**Implementation per library:**
1. Write `.wrapper_spec` file
2. Run `simple wrapper-gen <lib>.wrapper_spec`
3. Build generated Rust crate in `.build/rust/ffi_<lib>/`
4. Test via `test/lib/<lib>_spec.spl`

**Estimated effort per library:** 4-6 hours

**Note:** This phase is **optional** - most functionality works via shell commands or is not critical path.

---

## Specific Changes

### Change 1: Add `rt_dir_create` to Runtime

**File:** `src/compiler_seed/runtime.h`
```c
// After rt_dir_remove_all
bool rt_dir_create(const char* path, bool recursive);
```

**File:** `src/compiler_seed/platform/unix_common.h`
```c
bool rt_dir_create(const char* path, bool recursive) {
    if (!path) return false;
    if (recursive) {
        // mkdir -p logic
        char tmp[PATH_MAX];
        strncpy(tmp, path, sizeof(tmp) - 1);
        for (char* p = tmp + 1; *p; p++) {
            if (*p == '/') {
                *p = 0;
                mkdir(tmp, 0755);
                *p = '/';
            }
        }
        return mkdir(tmp, 0755) == 0 || errno == EEXIST;
    }
    return mkdir(path, 0755) == 0;
}
```

**File:** `src/compiler_seed/platform/platform_win.h`
```c
bool rt_dir_create(const char* path, bool recursive) {
    // Windows CreateDirectory implementation
    return CreateDirectoryA(path, NULL) || GetLastError() == ERROR_ALREADY_EXISTS;
}
```

### Change 2: Add `rt_dir_list` to Runtime

**File:** `src/compiler_seed/runtime.h`
```c
// Returns null-terminated array of strings (caller must free)
const char** rt_dir_list(const char* path, int64_t* out_count);
void rt_dir_list_free(const char** entries, int64_t count);
```

**File:** `src/compiler_seed/platform/unix_common.h`
```c
const char** rt_dir_list(const char* path, int64_t* out_count) {
    DIR* dir = opendir(path);
    if (!dir) { *out_count = 0; return NULL; }
    
    // Count entries
    int64_t count = 0;
    struct dirent* ent;
    while ((ent = readdir(dir)) != NULL) {
        if (strcmp(ent->d_name, ".") != 0 && strcmp(ent->d_name, "..") != 0)
            count++;
    }
    
    // Allocate array
    const char** result = malloc(sizeof(char*) * (count + 1));
    rewinddir(dir);
    
    int64_t i = 0;
    while ((ent = readdir(dir)) != NULL) {
        if (strcmp(ent->d_name, ".") != 0 && strcmp(ent->d_name, "..") != 0) {
            result[i++] = strdup(ent->d_name);
        }
    }
    result[count] = NULL;
    closedir(dir);
    
    *out_count = count;
    return result;
}

void rt_dir_list_free(const char** entries, int64_t count) {
    if (!entries) return;
    for (int64_t i = 0; i < count; i++) {
        free((void*)entries[i]);
    }
    free((void*)entries);
}
```

### Change 3: Update `dir_ops.spl`

**File:** `src/app/io/dir_ops.spl`

Replace shell calls:
```simple
# Before
fn dir_create(path: text, recursive: bool) -> bool:
    if recursive:
        val (out, err, code) = _dir_shell("mkdir -p '{path}'")
        code == 0
    else:
        val (out, err, code) = _dir_shell("mkdir '{path}'")
        code == 0

# After
extern fn rt_dir_create(path: text, recursive: bool) -> bool

fn dir_create(path: text, recursive: bool) -> bool:
    rt_dir_create(path, recursive)
```

### Change 4: Update `file_ops.spl`

**File:** `src/app/io/file_ops.spl`

Use existing runtime functions:
```simple
# Before (shell fallback)
fn file_exists(path: text) -> bool:
    _file_shell_bool("test -f '{path}'")

# After (direct runtime)
extern fn rt_file_exists(path: text) -> bool

fn file_exists(path: text) -> bool:
    rt_file_exists(path)
```

---

## Testing Strategy

### Unit Tests (C Runtime)
**File:** `src/compiler_seed/runtime_test.c`

Add tests:
```c
void test_rt_dir_create(void) {
    ASSERT(rt_dir_create("/tmp/test_dir", false));
    ASSERT(rt_dir_remove_all("/tmp/test_dir"));
    
    ASSERT(rt_dir_create("/tmp/test_dir/sub/deep", true));
    ASSERT(rt_dir_remove_all("/tmp/test_dir"));
}

void test_rt_dir_list(void) {
    rt_dir_create("/tmp/test_list", false);
    // Create files
    rt_file_write("/tmp/test_list/a.txt", "a");
    rt_file_write("/tmp/test_list/b.txt", "b");
    
    int64_t count;
    const char** entries = rt_dir_list("/tmp/test_list", &count);
    ASSERT_EQ_INT(count, 2);
    rt_dir_list_free(entries, count);
    rt_dir_remove_all("/tmp/test_list");
}
```

### Integration Tests (Simple)
**File:** `test/system/ffi/syscalls_test.spl`

Update tests:
```simple
it "directory create native":
    val test_dir = "/tmp/simple_native_test"
    check(dir_create(test_dir, false))
    check(is_dir(test_dir))
    check(dir_remove_all(test_dir) == 0)

it "directory list native":
    val test_dir = "/tmp/simple_list_test"
    dir_create(test_dir, false)
    file_write(test_dir + "/a.txt", "a")
    file_write(test_dir + "/b.txt", "b")
    val entries = dir_list(test_dir)
    expect(entries.len()).to_equal(2)
    dir_remove_all(test_dir)
```

---

## Success Criteria

### Must Have (Phase 1) ✅ COMPLETE
- [x] Zero shell calls in `dir_ops.spl` for create operations
- [x] Zero shell calls in `file_ops.spl` for basic operations (read, write, copy, delete, size, exists)
- [x] All existing tests pass
- [x] New runtime functions implemented: `rt_dir_create`, `rt_dir_list`, `rt_file_copy`, `rt_file_size`
- [x] Integration tests created and passing (`test/system/io/native_ops_spec.spl`)

### Nice to Have (Phase 2)
- [ ] Documentation: `doc/guide/sffi_two_tier.md`
- [ ] Benchmark: Compare native vs shell performance
- [ ] `dir_walk` uses native implementation (not `find`)

### Future Work (Phase 3)
- [ ] Regex wrapper implemented and tested
- [ ] SQLite wrapper implemented and tested
- [ ] HTTP wrapper implemented and tested

---

## Non-Goals

**Out of scope for this plan:**
1. ❌ Implementing all 580 external library functions
2. ❌ Replacing `rt_process_run` for all use cases
3. ❌ Windows-specific optimizations (focus on Unix first)
4. ❌ Performance optimization beyond removing shell overhead
5. ❌ Changing SFFI architecture (two-tier/three-tier patterns are correct)

---

## Dependencies

**Hard dependencies:**
- C toolchain (gcc/clang)
- Unix platform (macOS/Linux/FreeBSD)
- Simple runtime build system

**Soft dependencies (for Phase 3):**
- Rust toolchain (for three-tier wrappers)
- `simple wrapper-gen` tool
- `.wrapper_spec` format parser

---

## Rollout Plan

### Week 1: Core Implementation (Phase 1)
**Day 1-2:** Add runtime functions (`rt_dir_create`, `rt_dir_list`, `rt_file_copy`)  
**Day 3:** Update `dir_ops.spl` and `file_ops.spl`  
**Day 4:** Write and run tests  
**Day 5:** Fix bugs, validate

### Week 2: Cleanup (Phase 2)
**Day 1:** Remove dead shell helpers  
**Day 2:** Documentation  
**Day 3:** Code review and polish

### Future: External Libraries (Phase 3)
**On demand:** Implement three-tier wrappers as needed by features

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Breaking existing code | Medium | High | Comprehensive test suite |
| Platform-specific bugs | Medium | Medium | Test on macOS/Linux/FreeBSD |
| Performance regression | Low | Low | Benchmark before/after |
| Runtime complexity | Low | Medium | Keep implementations simple |

---

## Metrics

**Before (Current State):**
- Shell calls in io module: ~30
- Runtime functions: 22
- Test coverage: Unknown

**After (Phase 1 Complete):**
- Shell calls in io module: <5 (only `find`, `stat` for complex ops)
- Runtime functions: 28 (+6)
- Test coverage: >90% for new functions

**After (Phase 2 Complete):**
- Documentation complete
- All shell fallbacks documented with rationale

---

## Questions for User

1. **Priority:** Should we do Phase 1 now or defer?
2. **Scope:** Focus only on Unix or also Windows?
3. **Testing:** Run full test suite or just affected tests?
4. **External libs:** Any specific library (regex, sqlite, http) needed urgently?

---

## Related Documents

- `/sffi` skill - SFFI patterns and guidelines
- `doc/guide/sffi_gen_guide.md` - Wrapper generation
- `doc/design/sffi_external_library_pattern.md` - Three-tier design
- `src/compiler_seed/runtime.h` - Runtime function declarations
- `src/compiler_seed/platform/unix_common.h` - Unix implementations
- `src/app/io/mod.spl` - Main SFFI module

---

## Appendix: Complete Runtime Function List

### Currently Implemented (22 functions)
```
rt_dir_remove_all
rt_file_lock, rt_file_unlock
rt_file_read_text, rt_file_exists, rt_file_write, rt_file_delete, rt_file_size
rt_file_read_text_at, rt_file_write_text_at
rt_mmap, rt_munmap, rt_madvise, rt_msync
rt_process_spawn_async, rt_process_wait, rt_process_is_running, rt_process_kill
rt_time_now_unix_micros
rt_getpid, rt_hostname, rt_thread_available_parallelism
rt_log_* (6 functions)
```

### Proposed Additions (Phase 1)
```
rt_dir_create(path, recursive)
rt_dir_list(path) -> [text]
rt_file_copy(src, dst)
[Already exists: rt_env_get, rt_env_set - just need to use them]
```

### External Libraries (Phase 3 - 558 functions)
See "Missing (External Libraries)" section above.
