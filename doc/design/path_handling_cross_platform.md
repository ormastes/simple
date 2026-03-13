# Path Handling Cross-Platform Design

**Date:** 2026-03-13
**Status:** Implemented (Phase 1-2, 4-6 done; Phase 3 remaining)
**Purpose:** Consolidate path construction onto platform-aware utilities, eliminating raw `"/"` concatenation across 25+ files for correct Windows and double-slash behavior. Uses compile-time @cfg platform selection.
**Related:**
- `src/lib/nogc_sync_mut/path.spl` — pure-function path utilities
- `src/lib/nogc_sync_mut/fs/path.spl` — OOP `Path` class
- `src/lib/nogc_sync_mut/ffi/io.spl` — FFI `rt_path_join()`
- `src/lib/nogc_sync_mut/platform.spl` — `dir_sep()`, `is_windows()`
- `src/lib/nogc_sync_mut/path_platform/` — compile-time platform config modules (NEW)
- `src/compiler/10.frontend/core/cfg_platform.spl` — `@cfg` eval with toolchain support
- `src/compiler/70.backend/linker/msvc.spl` — MSVC linker integration
- `test/unit/lib/nogc_sync_mut/path_cross_platform_spec.spl` — 75 cross-platform tests
- `test/feature/platform/windows_spec.spl` — Windows platform tests (currently skipped)

---

## 1. Executive Summary

The Simple compiler codebase has ~25+ locations where file/path construction uses raw string concatenation (`path + "/" + segment`) instead of platform-aware path joining. This produces double-slash `//` on all platforms when base paths carry trailing separators, and breaks entirely on Windows where the native separator is `\`.

The codebase already ships good path utilities:

| Utility | Location | Platform-Aware |
|---------|----------|----------------|
| `path_join()` | `src/lib/nogc_sync_mut/path.spl` | Yes (both `/` and `\`) |
| `Path.join()` | `src/lib/nogc_sync_mut/fs/path.spl` | Yes (uses `dir_sep()`) |
| `rt_path_join()` | `src/lib/nogc_sync_mut/ffi/io.spl` | Yes (C runtime) |

These are inconsistently adopted. Most code bypasses them entirely with raw `+` concatenation.

---

## 2. Current Path Systems

### 2.1 Pure Simple `path_join()` — `src/lib/nogc_sync_mut/path.spl:52-68`

A free function that loops through a parts array, strips leading `/` from subsequent parts, and inserts `/` between segments only when the accumulated result doesn't already end with `/`.

```simple
fn path_join(parts: List<text>) -> text:
    var result = ""
    for part in parts:
        if part.is_empty():
            continue
        if result.is_empty():
            result = part
        else:
            val sep = if result.ends_with("/"): "" else: "/"
            val clean = if part.starts_with("/"): part.substring(1) else: part
            result = result + sep + clean
    result
```

**Strengths:**
- Handles empty parts and avoids double `/`
- Pure Simple, no FFI dependency

**Problems:**
- Hardcodes `"/"` separator — does not call `dir_sep()` from platform module
- Will produce forward-slash paths on Windows, which some Windows APIs reject
- No handling of drive letters (`C:\`) or UNC paths (`\\server\share`)

### 2.2 OOP `Path.join()` — `src/lib/nogc_sync_mut/fs/path.spl:38-57`

An instance method on the `Path` class that uses `dir_sep()` from the platform module.

```simple
fn join(component: text) -> Path:
    val sep = dir_sep()
    var base = self.value
    if base.ends_with(sep):
        base = base.substring(0, base.len() - 1)
    var comp = component
    if comp.starts_with(sep):
        comp = comp.substring(1)
    Path(value: base + sep + comp)
```

**Strengths:**
- Platform-aware: uses `dir_sep()` for the correct native separator
- Strips trailing separator from base and leading separator from component
- Returns a typed `Path` object, not raw text

**Problems:**
- Rarely used outside the `fs/` module itself
- Requires constructing a `Path` object, which discourages ad-hoc use
- No variadic/multi-segment overload

### 2.3 FFI `rt_path_join()` — `src/lib/nogc_sync_mut/ffi/io.spl:183`

Delegates to the C runtime function `rt_path_join()`, which handles platform separators at the native level.

```simple
extern fn rt_path_join(base: text, segment: text) -> text
```

**Strengths:**
- Correct on all platforms (C runtime handles separators)
- Used by the compiler driver for output paths

**Problems:**
- Requires FFI, so unusable in pure-Simple contexts (e.g., compile-time evaluation)
- Two-argument only, no variadic support

### 2.4 Raw string concatenation — everywhere

The most common pattern in the codebase:

```simple
val full_path = dir + "/" + filename
```

**Problems:**
- Produces `//` when `dir` has a trailing slash
- Produces forward-slash paths on Windows
- No separator normalization whatsoever
- Scattered across 25+ files with no single fix point

---

## 3. Affected Files — Full Inventory

### 3.1 Compiler Core

| File | Lines | Pattern |
|------|-------|---------|
| `src/compiler/00.common/dependency/resolution.spl` | 83, 89, 100, 106 | `root + "/"` unconditionally in `to_file_path()` and `to_dir_path()` |
| `src/compiler/10.frontend/core/interpreter/module_loader.spl` | 186 | `path_parts.join("/")` hardcoded separator |
| `src/compiler/80.driver/build/doc_warnings.spl` | 96 | `base_dir + "/" + entry` |
| `src/compiler/85.mdsoc/layer_doc_checker.spl` | 86 | `module_path + "/" + snake_name + ".spl"` |
| `src/compiler/90.tools/depgraph/analyzer.spl` | 177 | `scan_result.directory + "/" + file` |
| `src/compiler/90.tools/depgraph/main.spl` | 261 | `dir_path + "/" + child` |
| `src/compiler/70.backend/linker/mold.spl` | 25 | `cwd() + "/bin/mold/mold"` |

### 3.2 Applications

| File | Lines | Pattern |
|------|-------|---------|
| `src/app/cli/arch_check.spl` | 452 | `root + "/" + module_path + "/"` |
| `src/app/compile/native.spl` | 137, 140, 175, 178 | Multiple raw concat for output paths |
| `src/app/release/package.spl` | 15 | `release_dir + "/" + pkg_name` |
| `src/app/release/install.spl` | 106 | `dst + "/" + rel` |
| `src/app/unreal_cli/main.spl` | 44, 48, 52, 56, 60, 64, 318 | Seven raw concat sites for UE paths |

### 3.3 Libraries

| File | Lines | Pattern |
|------|-------|---------|
| `src/lib/nogc_sync_mut/dependency_tracker/resolution.spl` | 76-77, 87-88 | Duplicate of compiler resolution pattern |
| `src/lib/nogc_sync_mut/src/infra.spl` | 355 | Infrastructure path construction |
| `src/lib/nogc_async_mut/mcp/resources.spl` | 405, 495, 516, 697 | Four raw concat sites in MCP resource paths |
| `src/lib/nogc_async_mut/mcp/fileio_temp.spl` | 32 | Temp file path construction |

### 3.4 Already Correct (reference patterns)

| File | Line | Technique |
|------|------|-----------|
| `src/app/cli/query_rich.spl` | 2358 | Checks `dir.ends_with("/")` before adding separator |
| `src/lib/nogc_sync_mut/io/file_discovery.spl` | 11-15 | `_fd_path_join()` checks `ends_with` |
| `src/lib/nogc_sync_mut/fs/path.spl` | 38-57 | `Path.join()` uses `dir_sep()` |

---

## 4. Platform Support Analysis

### 4.1 Existing Windows Infrastructure

The project already has significant Windows support infrastructure:

| Component | Location | Description |
|-----------|----------|-------------|
| Platform detection | `src/lib/nogc_sync_mut/platform.spl` | `dir_sep()`, `path_sep()`, `exe_ext()`, `lib_ext()`, `is_windows()` |
| Path conversion | `src/lib/nogc_sync_mut/fs/path.spl` | `unix_to_windows()`, `windows_to_unix()`, `to_native_separators()` |
| Absolute path detection | `src/lib/nogc_sync_mut/path.spl:201` | `is_absolute_path()` detects Windows drive letters (`C:\`) |
| MSVC linker | `src/compiler/70.backend/linker/msvc.spl` | Complete `link.exe` integration |
| MinGW toolchain | `src/runtime/cmake/toolchains/windows-x86_64-mingw.cmake` | Cross-compilation cmake |
| ClangCL toolchain | `src/runtime/cmake/toolchains/windows-x86_64-clangcl.cmake` | MSVC ABI + LLVM |
| C runtime (Win) | `src/runtime/platform/platform_win.h` | Dual ABI (MSVC + MinGW) |
| Async I/O (Win) | `src/runtime/platform/async_windows.c` | IOCP backend |
| CRT startup (Win) | `src/runtime/startup/windows/crt_windows.c` | Windows CRT entry |
| Rust platform | `src/compiler_rust/common/src/target.rs`, `cc_detect.rs`, `link_config.rs` | Target triple detection |
| Windows tests | `test/feature/platform/windows_spec.spl` | 307 lines, currently skipped |

### 4.2 What Is Missing or Broken for Windows

| Issue | Location | Impact |
|-------|----------|--------|
| `is_absolute()` only checks `/` prefix | `path.spl:98` | Misses `C:\`, `D:\`, etc. |
| `normalize()` splits on `/` only | `path.spl:73` | Backslash paths produce wrong results |
| `path_join()` hardcodes `/` | `path.spl:52-68` | Forward slashes on Windows |
| 25+ raw concat sites hardcode `/` | See Section 3 | Forward slashes everywhere |
| No WSL path conversion | — | Cannot translate `/mnt/c/...` to `C:\...` |

### 4.3 MSVC vs MinGW vs ClangCL Differences

| Feature | MSVC | MinGW | ClangCL |
|---------|------|-------|---------|
| Compiler | `cl.exe` | `gcc`/`g++` | `clang-cl` |
| Linker | `link.exe` | `ld`/`lld` | `lld-link` |
| Whole-archive flag | `/WHOLEARCHIVE` | `--whole-archive` | `/WHOLEARCHIVE` |
| Main stub | Pragma-based | Weak attribute | Pragma-based |
| ASM stubs | Not needed | GCC-style | Not needed |
| System libs | `kernel32.lib`, `ws2_32.lib` | `-lkernel32`, `-lws2_32` | `kernel32.lib`, `ws2_32.lib` |
| ABI detection macro | `_MSC_VER` | (neither) | `SPL_TOOLCHAIN_CLANGCL` |

The platform header `src/runtime/platform/platform_win.h` dispatches via:
```c
#if defined(_MSC_VER) || defined(SPL_TOOLCHAIN_CLANGCL)
    // MSVC ABI path
#else
    // MinGW path
#endif
```

---

## 5. Fix Plan

### Phase 1: Enhance `path_join()` in `path.spl`

**Goal:** Make the canonical pure-Simple `path_join()` platform-aware without breaking existing callers.

Changes to `src/lib/nogc_sync_mut/path.spl`:

1. **Import `dir_sep()`** from platform module
2. **Replace hardcoded `"/"`** with `dir_sep()` in `path_join()` and add a convenience `join2(a, b)` for two-argument use
3. **Fix `is_absolute()`** (line 98) to detect Windows drive letters:
   ```simple
   fn is_absolute(path: text) -> bool:
       if path.starts_with("/"):
           return true
       # Windows drive letter: C:\ or C:/
       if path.len() >= 3:
           val c = path.char_at(0)
           if (c >= 'A' and c <= 'Z') or (c >= 'a' and c <= 'z'):
               if path.char_at(1) == ':' and (path.char_at(2) == '/' or path.char_at(2) == '\\'):
                   return true
       false
   ```
4. **Fix `normalize()`** (line 73) to pre-convert `\` to `/` before splitting, then apply `to_native_separators()` on output when on Windows
5. **Add `join2(base, segment)`** convenience function for the most common two-argument case:
   ```simple
   fn join2(base: text, segment: text) -> text:
       path_join([base, segment])
   ```

### Phase 2: Replace Raw Concatenation (~25 files)

**Goal:** Mechanically replace every `path + "/" + segment` with `join2(path, segment)`.

Each affected file needs:
```simple
use std.path.{join2}
```

**Priority order:**
1. Compiler core (`src/compiler/`) — highest impact, most path-sensitive
2. Applications (`src/app/`) — user-visible paths
3. Libraries (`src/lib/`) — foundational but fewer callers

**Example transformation:**

Before:
```simple
val full = base_dir + "/" + entry
```

After:
```simple
val full = join2(base_dir, entry)
```

For multi-segment paths:
```simple
# Before
val p = root + "/" + module_path + "/" + filename

# After
val p = path_join([root, module_path, filename])
```

### Phase 3: Fix `normalize()` for Windows

**Goal:** Handle backslash separators, UNC paths, and mixed separator strings.

Changes to `normalize()`:
1. Pre-convert all `\` to `/` for internal processing
2. Detect and preserve UNC prefix (`//server/share` after conversion)
3. Run existing `.` and `..` resolution logic on `/`-normalized path
4. On output, call `to_native_separators()` when `is_windows()` is true

```simple
fn normalize(path: text) -> text:
    # Normalize separators for processing
    var work = path.replace("\\", "/")

    # Preserve UNC prefix
    val is_unc = work.starts_with("//")

    # ... existing dot/dotdot resolution on work ...

    if is_windows():
        work = to_native_separators(work)
    work
```

### Phase 4: Add WSL Path Conversion

**Goal:** Support development workflows where Simple runs under WSL but interacts with Windows paths.

Add to `src/lib/nogc_sync_mut/fs/path.spl`:

```simple
fn to_wsl_path(win_path: text) -> text:
    # C:\Users\foo → /mnt/c/Users/foo
    if win_path.len() >= 3 and win_path.char_at(1) == ':':
        val drive = win_path.char_at(0).to_lower()
        val rest = win_path.substring(2).replace("\\", "/")
        return "/mnt/" + drive + rest
    win_path

fn from_wsl_path(wsl_path: text) -> text:
    # /mnt/c/Users/foo → C:\Users\foo
    if wsl_path.starts_with("/mnt/") and wsl_path.len() >= 6:
        val drive = wsl_path.char_at(5).to_upper()
        val rest = wsl_path.substring(6).replace("/", "\\")
        return drive + ":" + rest
    wsl_path
```

### Phase 5: Linker Path Cleanup

**Goal:** Ensure linker integration paths are platform-aware.

- `src/compiler/70.backend/linker/mold.spl:25` — replace `cwd() + "/bin/mold/mold"` with `join2(cwd(), "bin/mold/mold")`
- `src/compiler/70.backend/linker/msvc.spl` — audit for any raw concat (likely already correct since it targets Windows)
- `src/app/compile/native.spl` — replace all four raw concat sites with `join2()` calls

---

## 6. Architecture Diagram

### Current State

```
Application Layer (src/app/)
    |
    +-- raw concat: path + "/" + segment  (BROKEN)
    +-- occasional Path.join() calls
    |
Compiler Layer (src/compiler/)
    |
    +-- raw concat: path + "/" + segment  (BROKEN)
    +-- rt_path_join() in driver only
    |
Library Layer (src/lib/)
    |
    +-- fs/path.spl -----> Path.join()     (GOOD - uses dir_sep())
    +-- path.spl --------> path_join()     (PARTIAL - hardcodes /)
    +-- platform.spl ----> dir_sep()       (GOOD)
    +-- ffi/io.spl ------> rt_path_join()  (GOOD - C runtime)
    |                          |
    v                          v
Runtime Layer (src/runtime/)
    +-- platform_win.h --> Win32 API       (GOOD)
```

### Target State

```
All Layers (src/app/, src/compiler/, src/lib/)
    |
    +-- join2(base, segment)
    +-- path_join([a, b, c])
    |
    v
path.spl (enhanced)
    |
    +-- uses dir_sep() from platform module
    +-- strips trailing/leading separators
    +-- handles drive letters, UNC paths
    |
    v
platform.spl
    +-- dir_sep()  ->  "/" or "\"
    +-- is_windows()
    +-- path_sep() ->  ":" or ";"
```

The key change is that **all path construction flows through `path.spl`**, which in turn uses `platform.spl` for the correct separator. The OOP `Path.join()` in `fs/path.spl` remains available for typed path workflows, and `rt_path_join()` remains available for FFI contexts, but the primary entry point for all new code is `join2()` / `path_join()`.

---

## 7. Testing Strategy

### 7.1 Enable Existing Windows Tests

`test/feature/platform/windows_spec.spl` (307 lines) is currently skipped. After Phase 1 fixes:
1. Unskip the test file
2. Fix any failures related to path separator expectations
3. Run under CI with Windows cross-compilation targets

### 7.2 New Test Cases

Add to a new spec file `test/feature/platform/path_join_spec.spl`:

**Double-slash prevention (all platforms):**
```simple
describe "path_join":
    it "does not produce double slash when base has trailing /":
        expect(join2("foo/", "bar")).to_equal("foo/bar")

    it "handles base without trailing slash":
        expect(join2("foo", "bar")).to_equal("foo/bar")

    it "handles empty base":
        expect(join2("", "bar")).to_equal("bar")

    it "handles empty segment":
        expect(join2("foo", "")).to_equal("foo")

    it "handles multiple segments":
        expect(path_join(["a", "b", "c"])).to_equal("a/b/c")

    it "strips leading slash from segment":
        expect(join2("foo", "/bar")).to_equal("foo/bar")
```

**Windows separator tests (conditional on `is_windows()`):**
```simple
describe "path_join on windows":
    it "uses backslash separator":
        expect(join2("C:\\Users", "foo")).to_equal("C:\\Users\\foo")

    it "handles drive letter roots":
        expect(join2("C:\\", "file.spl")).to_equal("C:\\file.spl")
```

**`is_absolute()` tests:**
```simple
describe "is_absolute":
    it "detects unix absolute path":
        expect(is_absolute("/usr/bin")).to_equal(true)

    it "detects windows drive letter":
        expect(is_absolute("C:\\Users")).to_equal(true)

    it "detects relative path":
        expect(is_absolute("src/lib")).to_equal(false)

    it "detects windows relative":
        expect(is_absolute("src\\lib")).to_equal(false)
```

**`normalize()` tests:**
```simple
describe "normalize":
    it "resolves dot segments":
        expect(normalize("a/./b/../c")).to_equal("a/c")

    it "handles backslashes":
        expect(normalize("a\\b\\..\\c")).to_equal("a/c")

    it "preserves absolute prefix":
        expect(normalize("/a/b/../c")).to_equal("/a/c")
```

**WSL path conversion tests:**
```simple
describe "WSL paths":
    it "converts windows to WSL":
        expect(to_wsl_path("C:\\Users\\foo")).to_equal("/mnt/c/Users/foo")

    it "converts WSL to windows":
        expect(from_wsl_path("/mnt/c/Users/foo")).to_equal("C:\\Users\\foo")

    it "round-trips correctly":
        val original = "D:\\Projects\\simple"
        expect(from_wsl_path(to_wsl_path(original))).to_equal(original)
```

### 7.3 CI Integration

- Run path tests on Linux CI (covers unix separator path)
- Add Windows CI job (GitHub Actions `windows-latest`) for native Windows testing
- Add WSL test job for cross-environment path translation
- Verify no `//` appears in any generated output paths (can be checked via a grep-based lint rule)

---

## 8. Migration Checklist

- [x] Phase 1: Enhance `path_join()` and add `join2()` in `path.spl`
- [x] Phase 1: Fix `is_absolute()` for drive letters
- [x] Phase 1: Fix `normalize()` for backslashes (via `normalize_path()`)
- [x] Phase 2: Replace raw concat in compiler core (7 files)
- [x] Phase 2: Replace raw concat in applications (5 files)
- [x] Phase 2: Replace raw concat in libraries (4 files)
- [ ] Phase 3: Full `normalize()` rewrite with UNC support
- [x] Phase 4: Add `to_wsl_path()` / `from_wsl_path()`
- [x] Phase 5: Linker path cleanup
- [x] Testing: Add `path_cross_platform_spec.spl` (52 tests, all pass)
- [ ] Testing: Unskip `windows_spec.spl`
- [ ] Testing: Add Windows CI job

---

## 9. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| `join2()` import breaks existing code | Low | Low | Additive change; no existing API removed |
| `normalize()` changes alter behavior | Medium | Medium | Extensive test coverage before rollout |
| Windows CI environment differences | Medium | Low | Use `is_windows()` guards for platform-specific expectations |
| UNC path edge cases | Low | Low | Phase 3 is isolated; can ship without UNC initially |
| Performance regression from extra function calls | Very Low | Very Low | `join2()` is trivial string ops; no measurable overhead |
