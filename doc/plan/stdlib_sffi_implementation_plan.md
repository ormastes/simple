# Standard Library & SFFI Implementation Plan
**Date:** 2026-02-07
**Goal:** Increase test pass rate from 82% (3,606/4,379) to 95%+ (4,160+/4,379)
**Target:** Fix 554+ failing tests by implementing missing stdlib and SFFI features
**Version:** 0.5.0-rc.2

---

## Executive Summary

Current test suite status shows **773 failing tests** across 460 test files. Analysis reveals that **~554 failures** (72%) can be fixed by implementing missing features in pure Simple with SFFI wrappers. The remaining **~219 failures** (28%) require runtime interpreter fixes or are due to fundamental language limitations.

**This plan focuses on the 554 fixable failures**, organized into 5 implementation phases with clear priorities, file locations, and success metrics.

---

## Analysis Overview

### Failure Categories (773 total)

| Category | Count | Fixable | Approach | Priority |
|----------|-------|---------|----------|----------|
| String methods & conversions | ~95 | ✅ 95 | Pure Simple + SFFI | **High** |
| Missing stdlib functions | ~200 | ✅ 180 | Pure Simple + SFFI | **High** |
| `.new()` constructor antipattern | ~200 | ⚠️ 50 | Refactor tests | **Medium** |
| Runtime bugs (Dict.get, closures) | ~150 | ❌ 0 | Workarounds only | **Low** |
| Language limitations (exceptions) | ~50 | ⚠️ 30 | Partial workarounds | **Low** |
| Reserved word conflicts | ~15 | ✅ 15 | Rename identifiers | **Low** |
| Unimplemented SFFI stubs | ~63 | ✅ 63 | SFFI implementation | **Medium** |

**Total Fixable:** ~433 direct fixes + ~121 partial fixes = **~554 failures addressable**

---

## Implementation Phases

### **Phase 1: Critical String & Type Conversions** (Priority: High, ~95 failures)

**Goal:** Fix string methods and type conversion issues
**Estimated Effort:** 4-6 hours
**Files Modified:** `src/std/text.spl` (new), `src/std/convert.spl` (new), `src/app/io/mod.spl`

#### 1.1 String Methods (Pure Simple)
**Location:** `src/std/text.spl` (create new file)

```simple
# String extension methods
fn text_hash(s: text) -> i64:
    # Implement FNV-1a hash or call SFFI rt_text_hash
    var hash = 2166136261  # FNV offset basis
    for c in s:
        hash = (hash xor c.to_int()) * 16777619  # FNV prime
    hash

fn text_trim_start_matches(s: text, pattern: text) -> text:
    var result = s
    while result.starts_with(pattern):
        result = result[pattern.len():]
    result

fn text_trim_end_matches(s: text, pattern: text) -> text:
    var result = s
    while result.ends_with(pattern):
        result = result[0:result.len() - pattern.len()]
    result

fn text_contains_char(s: text, ch: text) -> bool:
    for c in s:
        if c == ch:
            return true
    false

fn text_index_of_char(s: text, ch: text) -> i64:
    var i = 0
    for c in s:
        if c == ch:
            return i
        i = i + 1
    -1
```

**Tests affected:** `test/lib/std/unit/set_spec.spl`, string manipulation tests
**Success metric:** +45 passing tests

#### 1.2 Type Conversions (Pure Simple + SFFI)
**Location:** `src/std/convert.spl` (create new file)

```simple
# Unsigned integer parsing
fn parse_u16(s: text) -> i64:
    val num = s.trim().parse_i64() ?? 0
    if num < 0 or num > 65535:
        0
    else:
        num

fn parse_u32(s: text) -> i64:
    val num = s.trim().parse_i64() ?? 0
    if num < 0 or num > 4294967295:
        0
    else:
        num

fn parse_u64(s: text) -> i64:
    # Limited to i64 max for now
    val num = s.trim().parse_i64() ?? 0
    if num < 0:
        0
    else:
        num

# Integer type conversions
fn i64_to_usize(n: i64) -> i64:
    if n < 0:
        0
    else:
        n

fn usize_to_i64(n: i64) -> i64:
    n  # No-op for now, runtime uses i64 for all integers
```

**SFFI Addition** (in `src/app/io/mod.spl`):
```simple
extern fn rt_text_hash(s: text) -> i64
fn text_hash_native(s: text) -> i64:
    rt_text_hash(s)
```

**Tests affected:** Type conversion tests, unsigned integer tests
**Success metric:** +50 passing tests

---

### **Phase 2: Collection Methods** (Priority: High, ~60 failures)

**Goal:** Add missing array/collection methods
**Estimated Effort:** 3-4 hours
**Files Modified:** `src/std/array.spl` (new)

#### 2.1 Array Extensions (Pure Simple)
**Location:** `src/std/array.spl` (create new file)

```simple
# Array utility methods
fn array_position<T>(arr: [T], predicate: fn(T) -> bool) -> i64:
    var i = 0
    for item in arr:
        if predicate(item):
            return i
        i = i + 1
    -1

fn array_enumerate<T>(arr: [T]) -> [(i64, T)]:
    var result = []
    var i = 0
    for item in arr:
        result = result.push((i, item))
        i = i + 1
    result

fn array_zip<T, U>(arr1: [T], arr2: [U]) -> [(T, U)]:
    var result = []
    val min_len = if arr1.len() < arr2.len(): arr1.len() else: arr2.len()
    var i = 0
    while i < min_len:
        result = result.push((arr1[i], arr2[i]))
        i = i + 1
    result

fn array_find<T>(arr: [T], predicate: fn(T) -> bool) -> T:
    for item in arr:
        if predicate(item):
            return item
    nil  # Or use Option<T> if available

fn array_sort_by<T>(arr: [T], comparator: fn(T, T) -> i64) -> [T]:
    # Simple insertion sort (workaround for Bug #19)
    var sorted = []
    for item in arr:
        var inserted = false
        var i = 0
        while i < sorted.len() and not inserted:
            if comparator(item, sorted[i]) < 0:
                # Insert at position i
                val before = sorted[0:i]
                val after = sorted[i:]
                sorted = before.push(item).merge(after)
                inserted = true
            i = i + 1
        if not inserted:
            sorted = sorted.push(item)
    sorted
```

**Tests affected:** Collection tests, array manipulation tests
**Success metric:** +60 passing tests

---

### **Phase 3: Math Functions** (Priority: Medium, ~30 failures)

**Goal:** Complete math stdlib with all trig, log, and rounding functions
**Estimated Effort:** 2-3 hours
**Files Modified:** `src/std/math.spl` (new), `src/app/io/mod.spl`

#### 3.1 SFFI Math Functions
**Location:** `src/app/io/mod.spl` (add to existing SFFI section, around line 1000)

```simple
# Logarithm functions
extern fn rt_math_log(x: f64) -> f64
extern fn rt_math_log10(x: f64) -> f64
extern fn rt_math_log2(x: f64) -> f64

fn math_log(x: f64) -> f64:
    rt_math_log(x)

fn math_log10(x: f64) -> f64:
    rt_math_log10(x)

fn math_log2(x: f64) -> f64:
    rt_math_log2(x)

# Inverse trig functions
extern fn rt_math_asin(x: f64) -> f64
extern fn rt_math_acos(x: f64) -> f64
extern fn rt_math_atan(x: f64) -> f64
extern fn rt_math_atan2(y: f64, x: f64) -> f64

fn math_asin(x: f64) -> f64:
    rt_math_asin(x)

fn math_acos(x: f64) -> f64:
    rt_math_acos(x)

fn math_atan(x: f64) -> f64:
    rt_math_atan(x)

fn math_atan2(y: f64, x: f64) -> f64:
    rt_math_atan2(y, x)

# Hyperbolic functions
extern fn rt_math_sinh(x: f64) -> f64
extern fn rt_math_cosh(x: f64) -> f64
extern fn rt_math_tanh(x: f64) -> f64

fn math_sinh(x: f64) -> f64:
    rt_math_sinh(x)

fn math_cosh(x: f64) -> f64:
    rt_math_cosh(x)

fn math_tanh(x: f64) -> f64:
    rt_math_tanh(x)

# Rounding functions
extern fn rt_math_ceil(x: f64) -> f64
extern fn rt_math_floor(x: f64) -> f64
extern fn rt_math_round(x: f64) -> f64

fn math_ceil(x: f64) -> f64:
    rt_math_ceil(x)

fn math_floor(x: f64) -> f64:
    rt_math_floor(x)

fn math_round(x: f64) -> f64:
    rt_math_round(x)
```

#### 3.2 Pure Simple Math Utilities
**Location:** `src/std/math.spl` (create new file)

```simple
# Math utilities that don't need SFFI
fn math_abs(x: f64) -> f64:
    if x < 0.0: -x else: x

fn math_abs_i64(x: i64) -> i64:
    if x < 0: -x else: x

fn math_min(a: f64, b: f64) -> f64:
    if a < b: a else: b

fn math_max(a: f64, b: f64) -> f64:
    if a > b: a else: b

fn math_min_i64(a: i64, b: i64) -> i64:
    if a < b: a else: b

fn math_max_i64(a: i64, b: i64) -> i64:
    if a > b: a else: b

fn math_clamp(x: f64, min_val: f64, max_val: f64) -> f64:
    if x < min_val: min_val
    elif x > max_val: max_val
    else: x
```

**Tests affected:** `test/lib/std/unit/core/math_spec.spl`, DL tests
**Success metric:** +30 passing tests

---

### **Phase 4: System & Concurrency SFFI** (Priority: Medium, ~63 failures)

**Goal:** Implement stub SFFI functions and add thread/concurrency support
**Estimated Effort:** 3-4 hours
**Files Modified:** `src/app/io/mod.spl`

#### 4.1 Replace Stubs with Real Implementations
**Location:** `src/app/io/mod.spl` (update existing stubs)

**Current stubs to fix (lines 38-500):**

```simple
# System information - CURRENT STUBS
fn getpid() -> i64:
    12345  # STUB - return actual PID

fn hostname() -> text:
    "localhost"  # STUB - return actual hostname

fn cpu_count() -> i64:
    1  # STUB - return actual CPU count

# File operations - CURRENT STUBS
fn file_modified_time(path: text) -> i64:
    0  # STUB - return actual timestamp

fn file_hash_sha256(path: text) -> text:
    ""  # STUB - return actual SHA256 hash

fn dir_remove_all(path: text) -> i64:
    print "[INFO] dir_remove_all stub called: {path}"
    -1  # STUB - implement recursive delete

# Time operations - CURRENT STUBS
fn time_now_unix_micros() -> i64:
    0  # STUB - return actual microseconds

# Environment - CURRENT STUBS
fn env_set(key: text, value: text) -> bool:
    false  # STUB - implement env var setting
```

**SFFI Implementations:**

```simple
# System information - REAL IMPLEMENTATIONS
extern fn rt_getpid() -> i64
fn getpid() -> i64:
    rt_getpid()

extern fn rt_hostname() -> text
fn hostname() -> text:
    rt_hostname()

extern fn rt_cpu_count() -> i64
fn cpu_count() -> i64:
    rt_cpu_count()

# File operations - REAL IMPLEMENTATIONS
extern fn rt_file_modified_time(path: text) -> i64
fn file_modified_time(path: text) -> i64:
    rt_file_modified_time(path)

extern fn rt_file_hash_sha256(path: text) -> text
fn file_hash_sha256(path: text) -> text:
    rt_file_hash_sha256(path)

extern fn rt_dir_remove_all(path: text) -> bool
fn dir_remove_all(path: text) -> i64:
    if rt_dir_remove_all(path): 0 else: -1

# Time operations - REAL IMPLEMENTATIONS
extern fn rt_time_now_unix_micros() -> i64
fn time_now_unix_micros() -> i64:
    rt_time_now_unix_micros()

# Environment - REAL IMPLEMENTATIONS
extern fn rt_env_set(key: text, value: text) -> bool
fn env_set(key: text, value: text) -> bool:
    rt_env_set(key, value)
```

**Tests affected:** System tests, file metadata tests
**Success metric:** +20 passing tests

#### 4.2 Thread & Concurrency Functions
**Location:** `src/app/io/mod.spl` (add new section)

```simple
# --- Thread & Concurrency ---
extern fn rt_thread_available_parallelism() -> i64
fn thread_available_parallelism() -> i64:
    rt_thread_available_parallelism()

extern fn rt_thread_sleep_ms(duration_ms: i64)
fn thread_sleep_ms(duration_ms: i64):
    rt_thread_sleep_ms(duration_ms)

extern fn rt_thread_yield()
fn thread_yield():
    rt_thread_yield()

extern fn rt_thread_current_id() -> i64
fn thread_current_id() -> i64:
    rt_thread_current_id()
```

**Tests affected:** `test/lib/std/unit/concurrent_spec.spl`
**Success metric:** +40 passing tests

#### 4.3 Atomic Operations (Fix Stubs)
**Location:** `src/app/io/mod.spl` (update existing atomic stubs)

```simple
# Atomic operations - REAL IMPLEMENTATIONS
extern fn rt_atomic_i64_new(value: i64) -> i64
extern fn rt_atomic_i64_load(atomic_ref: i64) -> i64
extern fn rt_atomic_i64_store(atomic_ref: i64, value: i64)
extern fn rt_atomic_i64_fetch_add(atomic_ref: i64, value: i64) -> i64

fn atomic_i64_new(value: i64) -> i64:
    rt_atomic_i64_new(value)

fn atomic_i64_load(atomic_ref: i64) -> i64:
    rt_atomic_i64_load(atomic_ref)

fn atomic_i64_store(atomic_ref: i64, value: i64):
    rt_atomic_i64_store(atomic_ref, value)

fn atomic_i64_fetch_add(atomic_ref: i64, value: i64) -> i64:
    rt_atomic_i64_fetch_add(atomic_ref, value)
```

**Tests affected:** Atomic operation tests
**Success metric:** +3 passing tests

---

### **Phase 5: File/Path Operations** (Priority: Low, ~25 failures)

**Goal:** Add path manipulation utilities
**Estimated Effort:** 2-3 hours
**Files Modified:** `src/std/path.spl` (new)

#### 5.1 Path Utilities (Pure Simple)
**Location:** `src/std/path.spl` (create new file)

```simple
# Path manipulation utilities
fn path_normalize(path: text) -> text:
    # Remove redundant slashes and resolve . and ..
    var components = path.split("/")
    var normalized = []

    for component in components:
        if component == "." or component == "":
            pass  # Skip
        elif component == "..":
            if normalized.len() > 0:
                # Pop last component
                normalized = normalized[0:normalized.len() - 1]
        else:
            normalized = normalized.push(component)

    "/" + normalized.join("/")

fn path_resolve(path: text, base: text) -> text:
    # Make path absolute relative to base
    if path.starts_with("/"):
        path_normalize(path)
    else:
        path_normalize(base + "/" + path)

fn path_relative_to(path: text, base: text) -> text:
    # Get relative path from base to path
    val norm_path = path_normalize(path).split("/")
    val norm_base = path_normalize(base).split("/")

    # Find common prefix
    var i = 0
    val min_len = if norm_path.len() < norm_base.len(): norm_path.len() else: norm_base.len()
    while i < min_len and norm_path[i] == norm_base[i]:
        i = i + 1

    # Build relative path
    val up_count = norm_base.len() - i
    var result = []
    var j = 0
    while j < up_count:
        result = result.push("..")
        j = j + 1

    # Add remaining path components
    while i < norm_path.len():
        result = result.push(norm_path[i])
        i = i + 1

    result.join("/")

fn path_join(paths: [text]) -> text:
    path_normalize(paths.join("/"))

fn path_extension(path: text) -> text:
    val parts = path.split(".")
    if parts.len() > 1:
        parts[parts.len() - 1]
    else:
        ""

fn path_stem(path: text) -> text:
    val base = path_basename(path)
    val parts = base.split(".")
    if parts.len() > 1:
        parts[0:parts.len() - 1].join(".")
    else:
        base

fn path_basename(path: text) -> text:
    val parts = path.split("/")
    if parts.len() > 0:
        parts[parts.len() - 1]
    else:
        path

fn path_dirname(path: text) -> text:
    val parts = path.split("/")
    if parts.len() > 1:
        parts[0:parts.len() - 1].join("/")
    else:
        "."
```

**Tests affected:** `test/lib/std/unit/fs_spec.spl`, path tests
**Success metric:** +25 passing tests

---

## Workarounds for Unfixable Issues

### Reserved Word Conflicts (~15 failures)
**Location:** Test files with naming conflicts
**Fix:** Automated refactoring script

Create `scripts/fix_reserved_words.spl`:
```simple
#!/usr/bin/env simple
use app.io

fn fix_reserved_words(file_path: text):
    val content = file_read(file_path)

    # Replace reserved word parameters
    var fixed = content
    fixed = fixed.replace("fn (feature:", "fn (feat:")
    fixed = fixed.replace("fn (class:", "fn (cls:")
    fixed = fixed.replace("fn (val:", "fn (node:")
    fixed = fixed.replace(", feature:", ", feat:")
    fixed = fixed.replace(", class:", ", cls:")
    fixed = fixed.replace(", val:", ", node:")

    if fixed != content:
        file_write(file_path, fixed)
        print "Fixed: {file_path}"

fn main():
    val test_files = glob("test/**/*_spec.spl")
    for file in test_files:
        fix_reserved_words(file)
```

**Success metric:** +15 passing tests

### `.new()` Constructor Refactoring (~50 partial fixes)
**Location:** Test files using `.new()` pattern
**Fix:** Semi-automated refactoring

Create `scripts/fix_new_constructors.spl`:
```simple
#!/usr/bin/env simple
use app.io

fn fix_new_pattern(file_path: text):
    val content = file_read(file_path)

    # Simple pattern replacement (won't catch all cases)
    var fixed = content

    # Common patterns: Point.new(x: 3, y: 4) -> Point(x: 3, y: 4)
    # This is a heuristic - manual review needed
    val lines = content.split("\n")
    var new_lines = []

    for line in lines:
        var new_line = line
        if line.contains(".new("):
            # Extract pattern: ClassName.new(args) -> ClassName(args)
            # Simple regex-like replacement (manual verification needed)
            new_line = line.replace(".new(", "(")
        new_lines = new_lines.push(new_line)

    fixed = new_lines.join("\n")

    if fixed != content:
        file_write(file_path, fixed)
        print "Fixed: {file_path}"

fn main():
    val test_files = glob("test/**/*_spec.spl")
    for file in test_files:
        fix_new_pattern(file)

    print "\nWARNING: Manual review required for imported class constructors"
    print "See CLAUDE.md constructor section for patterns"
```

**Success metric:** +50 passing tests (partial, manual review needed)

---

## Testing Strategy

### Incremental Testing Approach

**After each phase:**
1. Run affected test files only (small batches)
2. Verify no regressions in passing tests
3. Update test count metrics

**Commands:**
```bash
# Phase 1: String & Type Conversions
bin/simple test test/lib/std/unit/set_spec.spl 2>/dev/null
bin/simple test test/lib/std/unit/string_spec.spl 2>/dev/null

# Phase 2: Collections
bin/simple test test/lib/std/unit/array_spec.spl 2>/dev/null
bin/simple test test/lib/std/unit/collections_spec.spl 2>/dev/null

# Phase 3: Math
bin/simple test test/lib/std/unit/core/math_spec.spl 2>/dev/null

# Phase 4: System & Concurrency
bin/simple test test/lib/std/unit/concurrent_spec.spl 2>/dev/null
bin/simple test test/lib/std/unit/process_spec.spl 2>/dev/null

# Phase 5: File/Path
bin/simple test test/lib/std/unit/fs_spec.spl 2>/dev/null
```

### Success Metrics

| Phase | Target Fixes | Test Files Affected | Success Metric |
|-------|--------------|---------------------|----------------|
| Phase 1 | +95 tests | 15-20 files | String/conversion tests pass |
| Phase 2 | +60 tests | 10-15 files | Collection tests pass |
| Phase 3 | +30 tests | 5-8 files | Math tests pass |
| Phase 4 | +63 tests | 10-12 files | System/concurrent tests pass |
| Phase 5 | +25 tests | 5-8 files | Path/fs tests pass |
| Workarounds | +65 tests | 30-50 files | Reserved word & .new() fixes |
| **TOTAL** | **+338 tests** | **75-113 files** | **Pass rate: 90%+ (3,944+/4,379)** |

---

## Implementation Scripts

### Central Implementation Script
**Location:** `scripts/impl_stdlib_sffi.spl`

```simple
#!/usr/bin/env simple
# Main implementation orchestrator
use app.io

fn run_phase(phase: i64, script_path: text):
    print "\n=== Running Phase {phase} ==="
    val result = process_run("bin/simple", [script_path])
    if result.2 == 0:
        print "✓ Phase {phase} completed"
    else:
        print "✗ Phase {phase} failed"
        print result.1  # stderr

fn main():
    print "Standard Library & SFFI Implementation"
    print "======================================"

    run_phase(1, "scripts/impl/phase1_string_convert.spl")
    run_phase(2, "scripts/impl/phase2_collections.spl")
    run_phase(3, "scripts/impl/phase3_math.spl")
    run_phase(4, "scripts/impl/phase4_system_sffi.spl")
    run_phase(5, "scripts/impl/phase5_path.spl")

    print "\n=== Running workarounds ==="
    run_phase(6, "scripts/fix_reserved_words.spl")
    run_phase(7, "scripts/fix_new_constructors.spl")

    print "\n=== Implementation Complete ==="
    print "Run: bin/simple test 2>/dev/null"
```

### Phase-Specific Scripts (in `scripts/impl/`)

Each phase gets its own implementation script:
- `scripts/impl/phase1_string_convert.spl` - Create `src/std/text.spl`, `src/std/convert.spl`
- `scripts/impl/phase2_collections.spl` - Create `src/std/array.spl`
- `scripts/impl/phase3_math.spl` - Create `src/std/math.spl`, update `src/app/io/mod.spl`
- `scripts/impl/phase4_system_sffi.spl` - Update `src/app/io/mod.spl` stubs
- `scripts/impl/phase5_path.spl` - Create `src/std/path.spl`

---

## Risk Assessment

### Low Risk (Pure Simple implementations)
- ✅ String utilities (no dependencies)
- ✅ Collection methods (simple algorithms)
- ✅ Path manipulation (string operations)
- ✅ Pure math utilities (abs, min, max)

### Medium Risk (SFFI wrappers)
- ⚠️ Math SFFI functions (need runtime support)
- ⚠️ System functions (platform-specific)
- ⚠️ Thread functions (concurrency complexity)

### High Risk (Requires runtime changes)
- ❌ Dict.get() returning Option (interpreter change)
- ❌ Closure variable capture (interpreter change)
- ❌ Unsigned integer types (type system change)

### Mitigations
1. **Test incrementally** - Run tests after each phase
2. **Keep backups** - jj snapshot before each phase
3. **Manual review** - Verify `.new()` refactoring manually
4. **Fallback stubs** - If SFFI fails, keep stub implementations

---

## Timeline Estimate

| Phase | Duration | Cumulative | Dependencies |
|-------|----------|------------|--------------|
| Phase 1 | 4-6 hours | 6h | None |
| Phase 2 | 3-4 hours | 10h | None |
| Phase 3 | 2-3 hours | 13h | None |
| Phase 4 | 3-4 hours | 17h | Phase 3 (math) |
| Phase 5 | 2-3 hours | 20h | None |
| Workarounds | 2-3 hours | 23h | All phases |
| Testing | 3-4 hours | 27h | All phases |
| **TOTAL** | **19-27 hours** | **27h max** | - |

**Recommended Approach:**
- Implement Phases 1-2 (10h) → Test → Review
- Implement Phases 3-5 (10h) → Test → Review
- Apply workarounds (3h) → Final test

---

## Next Steps

### Option A: Sequential Implementation (Recommended)
1. Review this plan document
2. Implement Phase 1 (4-6h)
3. Test Phase 1 results
4. Continue with Phase 2, etc.

### Option B: Parallel Team Implementation
1. Review this plan document
2. Create 5-agent team (one per phase)
3. Run phases 1-5 in parallel (~6-8h)
4. Consolidate and test results

### Option C: Plan Refinement
1. Review this document
2. Identify concerns or questions
3. Refine plan before implementation

---

## Appendix: File Locations Summary

**New files to create:**
- `src/std/text.spl` - String extension methods
- `src/std/convert.spl` - Type conversions
- `src/std/array.spl` - Collection methods
- `src/std/math.spl` - Pure math utilities
- `src/std/path.spl` - Path manipulation
- `scripts/impl_stdlib_sffi.spl` - Main orchestrator
- `scripts/impl/phase*.spl` - Phase-specific scripts (5 files)
- `scripts/fix_reserved_words.spl` - Workaround script
- `scripts/fix_new_constructors.spl` - Workaround script

**Files to modify:**
- `src/app/io/mod.spl` - Add SFFI functions, update stubs

**Total:** 9 new files, 1 modified file

---

**Plan Status:** Ready for review
**Next Action:** Choose implementation approach (A, B, or C)
