# @skip/@ignore Implementation Plan

**Document:** Implementation Roadmap
**Date:** 2026-02-08
**Status:** PLANNING
**Design Doc:** `doc/design/skip_ignore_decorator_system.md`

## Overview

Implement `@skip(platforms=..., runtimes=...)` and `@ignore(platforms=..., runtimes=...)` decorator system for test framework.

**Timeline:** 8 weeks (comprehensive function-based) + 2-4 weeks (parser attributes)
**Priority:** HIGH
**Scope:** Comprehensive skip/ignore system supporting ALL execution conditions
**Dependencies:** None (builds on existing spec.spl)

## Semantic Distinction

### `@skip` - "Will implement in future"

**Meaning:** The environment/platform **should be supported** but isn't implemented yet. This is a **TODO** item.

```simple
@skip(platforms: ["windows"], test_mode: ["interpreter"])
it "file permissions test":
    # This WILL work on Windows eventually
    # We just haven't implemented it yet
    chmod("/tmp/file", 0o644)
    check(get_permissions() == 0o644)
```

**Use cases:**
- Feature not yet ported to this platform
- Runtime mode not yet supported (e.g., interpreter mode needs work)
- Known bug that will be fixed

**Reporting:** Skipped tests are **counted** in test totals and reported as "SKIP" to track technical debt.

### `@ignore` - "Fundamentally not supported"

**Meaning:** The environment/platform is **fundamentally incompatible**. This will **never be fixed** because the underlying capability doesn't exist.

```simple
@ignore(platforms: ["windows"])
it "Unix fork test":
    # This will NEVER work on Windows
    # fork() is Unix-only API, no Windows equivalent
    pid = fork()
    check(pid > 0)
```

**Use cases:**
- Platform-specific APIs (fork on Unix, WinAPI on Windows)
- Hardware-specific features (GPU tests on CPU-only machines)
- Architectural impossibilities (32-bit pointer tests on 64-bit systems)

**Reporting:** Ignored tests are **NOT counted** in totals at all. They're completely silent, as if they don't exist on that platform.

### Quick Comparison

| Aspect | `@skip` | `@ignore` |
|--------|---------|-----------|
| **Intent** | Will implement in future | Fundamentally not supported |
| **Timeline** | Temporary (TODO) | Permanent (won't fix) |
| **Counted in totals** | ✅ Yes | ❌ No |
| **Output** | Shows "SKIP" message | Silent (no output) |
| **Example** | Feature not yet ported | Platform-specific API |
| **Technical debt** | Yes, track it | No, by design |

## Real-World Examples

### Example 1: Platform + Runtime Combinations
```simple
# Skip on Windows interpreter (will implement later)
val skip_win_interp = skip(
    platforms: ["windows"],
    runtimes: ["interpreter"],
    reason: "Windows interpreter support incomplete"
)

# Ignore on 32-bit architectures (fundamental limitation)
val ignore_32bit = ignore(
    architectures: ["x86", "arm32"],
    reason: "64-bit pointers required"
)
```

### Example 2: Hardware Requirements
```simple
# Skip GPU tests if no GPU detected
val skip_no_gpu = skip(
    hardware: ["gpu"],
    reason: "GPU acceleration not yet implemented for CPU fallback"
)

# Ignore SIMD tests on platforms without SIMD
val ignore_no_simd = ignore(
    hardware: ["avx2", "neon"],
    reason: "SIMD instructions required, no scalar implementation"
)
```

### Example 3: Feature Flags
```simple
# Skip async tests if async feature disabled
val skip_no_async = skip(
    features: ["async"],
    reason: "Async runtime not initialized"
)

# Ignore generics in interpreter
val ignore_generics = ignore(
    runtimes: ["interpreter"],
    features: ["generics"],
    reason: "Generics require static compilation"
)
```

### Example 4: Version Constraints
```simple
# Skip on older compiler versions
val skip_old_version = skip(
    version: "< 0.5.0",
    reason: "Requires v0.5.0+ for new syntax"
)
```

### Example 5: Complex Multi-Condition
```simple
# Network tests that require multiple conditions
val skip_network_test = skip(
    network: true,
    env_vars: {"CI": "true"},
    profiles: ["debug"],
    reason: "Network tests only in CI debug builds"
)

skip_network_test("API integration test", fn():
    val response = http_get("https://api.example.com")
    check(response.status == 200)
)
```

### Example 6: File System Features
```simple
# Skip symlink tests on Windows (will implement with junctions)
val skip_symlink_win = skip(
    platforms: ["windows"],
    fs_features: ["symlinks"],
    reason: "Need to implement junction support"
)

# Ignore permission tests on FAT32
val ignore_fat32_perms = ignore(
    fs_features: ["permissions"],
    reason: "FAT32 has no permission system"
)
```

## Goals

1. **Comprehensive condition support**: Platform, runtime, architecture, features, hardware, dependencies, environment, file system, network, version constraints
2. **Semantic distinction**: Clear skip (TODO) vs ignore (won't fix) semantics
3. **Accurate detection**: Fast, cached detection for all condition types
4. **Flexible composition**: AND/OR logic for complex conditions
5. **Performance**: < 1ms overhead per test
6. **Backward compatible**: Existing tests continue to work
7. **Clear migration**: Automated migration from old skip functions
8. **Comprehensive reporting**: Track skipped tests as technical debt

## Comprehensive Condition Support

The system supports ALL possible test execution conditions across multiple dimensions:

### 1. **Platform Conditions**
```simple
platforms: ["windows", "linux", "macos", "unix", "bsd", "solaris"]
```

### 2. **Runtime Mode**
```simple
runtimes: ["interpreter", "compiled", "jit", "aot"]
```

### 3. **Build Profile**
```simple
profiles: ["debug", "release", "bootstrap", "test"]
```

### 4. **Architecture**
```simple
architectures: ["x86_64", "aarch64", "arm64", "riscv64", "wasm32"]
```

### 5. **Feature Flags**
```simple
features: ["generics", "async", "macros", "effects", "inline_asm"]
```

### 6. **Compiler Version**
```simple
version: ">= 0.5.0"
version: "< 1.0.0"
version: "0.4.x"
```

### 7. **Hardware Capabilities**
```simple
hardware: ["gpu", "simd", "avx2", "neon", "multi_core"]
```

### 8. **Dependencies**
```simple
requires: ["torch", "numpy", "sqlite3"]
```

### 9. **Environment Variables**
```simple
env_vars: {"CI": "true", "SIMPLE_COVERAGE": nil}
```

### 10. **File System Capabilities**
```simple
fs_features: ["symlinks", "permissions", "case_sensitive", "xattr"]
```

### 11. **Network Availability**
```simple
network: true  # Requires internet connection
```

### 12. **Performance/Timing**
```simple
max_duration: "5s"  # Skip if expected to take longer
tags: ["slow", "quick", "integration", "unit"]
```

## Non-Goals (Future Work)

- Distributed test execution
- Test result database integration

## Implementation Phases

### Phase 1: Foundation (Week 1) ✅ PARTIALLY COMPLETE

**Status:** Platform detection done, runtime detection TODO

#### Task 1.1: Platform Detection ✅ DONE
- [x] `is_windows()` - Completed 2026-02-08
- [x] `is_linux()` - Completed 2026-02-08
- [x] `is_macos()` - Completed 2026-02-08
- [x] `is_unix()` - Completed 2026-02-08
- [ ] Architecture detection (`is_x86_64()`, `is_aarch64()`)
- [x] Caching layer - Basic caching in place

**Files Modified:**
- ✅ `src/std/spec.spl` (+40 lines for platform detection)

#### Task 1.2: Comprehensive Environment Detection ⏳ TODO

**1. Runtime Mode Detection:**
- [ ] Detect interpreter vs compiled mode
- [ ] Detect debug vs release build profile
- [ ] Detect JIT availability
- [ ] Detect AOT compilation

**2. Architecture Detection:**
- [ ] `is_x86_64()`, `is_aarch64()`, `is_arm64()`, `is_riscv64()`, `is_wasm32()`
- [ ] Detect pointer size (32-bit vs 64-bit)
- [ ] Detect endianness

**3. Feature Flag Detection:**
- [ ] Detect generics support
- [ ] Detect async/await support
- [ ] Detect macro system
- [ ] Detect effects system
- [ ] Detect inline assembly

**4. Hardware Capability Detection:**
- [ ] Detect GPU availability (CUDA, OpenCL, Metal)
- [ ] Detect SIMD support (AVX2, NEON, SSE)
- [ ] Detect CPU core count
- [ ] Detect memory size

**5. Dependency Detection:**
- [ ] Check for external libraries (via `dlopen`/`LoadLibrary`)
- [ ] Check for optional modules
- [ ] Version checking for dependencies

**6. Environment Detection:**
- [ ] Read environment variables
- [ ] Detect CI environment
- [ ] Detect test mode flags

**7. File System Detection:**
- [ ] Check symlink support
- [ ] Check permission system
- [ ] Check case sensitivity
- [ ] Check extended attributes

**8. Network Detection:**
- [ ] Check internet connectivity
- [ ] Check specific hosts reachable

**9. Version Detection:**
- [ ] Get compiler version
- [ ] Parse version constraints
- [ ] Semver comparison

**Files to Create:**
- `src/std/spec/env_detect.spl` (NEW - ~400 lines for all detection)
  - Platform detection (existing)
  - Runtime detection
  - Architecture detection
  - Feature detection
  - Hardware detection
  - Dependency detection
  - Environment detection
  - File system detection
  - Network detection
  - Version detection

**Structs:**
```simple
struct EnvInfo:
    platform: PlatformInfo
    runtime: RuntimeInfo
    architecture: ArchInfo
    features: FeatureInfo
    hardware: HardwareInfo
    fs: FileSystemInfo
    version: VersionInfo
```

**Deliverables:**
- Complete environment detection system
- All info structs with cached results
- 100+ unit tests for detection accuracy
- Performance benchmark (< 1ms total)

**Time Estimate:** 2 weeks (comprehensive implementation)

---

### Phase 2: Core Skip Logic (Week 2) ⏳ NOT STARTED

#### Task 2.1: SkipCondition Struct

**Implementation:**
```simple
struct SkipCondition:
    # Platform & Runtime
    platforms: [text]
    runtimes: [text]
    profiles: [text]
    architectures: [text]

    # Compiler Features
    features: [text]
    version: text

    # Hardware & Dependencies
    hardware: [text]
    requires: [text]

    # Environment & File System
    env_vars: {text: text}
    fs_features: [text]
    network: bool

    # Metadata
    tags: [text]
    reason: text
    ignore: bool

    fn matches() -> bool:
        """Evaluate if current environment matches ANY skip condition (OR logic)."""

        # Check each condition dimension
        val checks = [
            matches_platforms(self.platforms),
            matches_runtimes(self.runtimes),
            matches_profiles(self.profiles),
            matches_architectures(self.architectures),
            matches_features(self.features),
            matches_version(self.version),
            matches_hardware(self.hardware),
            matches_requires(self.requires),
            matches_env_vars(self.env_vars),
            matches_fs_features(self.fs_features),
            matches_network(self.network),
            matches_tags(self.tags)
        ]

        # Skip if ANY condition matches (OR logic)
        checks.any(\check: check)
```

**Files to Modify:**
- `src/std/spec.spl` (+60 lines)

**Tests:**
```simple
describe "SkipCondition":
    it "matches current platform":
        val cond = SkipCondition(
            platforms: ["linux"],
            runtimes: [],
            reason: "test",
            ignore: false
        )
        check(cond.matches() == true)  # On Linux
```

#### Task 2.2: Condition Evaluator

**Implementation:**
```simple
fn should_skip_test(platforms: [text], runtimes: [text]) -> bool:
    if platforms.len() == 0 and runtimes.len() == 0:
        return false  # No conditions = never skip

    val platform_info = get_platform_info()
    val runtime_info = get_runtime_info()

    # Check platform match
    var platform_matched = false
    if platforms.len() > 0:
        for platform in platforms:
            if platform_info.os == platform or
               (platform == "unix" and platform_info.is_unix):
                platform_matched = true

    # Check runtime match
    var runtime_matched = false
    if runtimes.len() > 0:
        for runtime in runtimes:
            if runtime_info.mode == runtime:
                runtime_matched = true

    # Skip if ANY condition matched
    platform_matched or runtime_matched

fn matches_platform(name: text, patterns: [text]) -> bool:
    # Helper for platform matching
    # ...

fn matches_runtime(name: text, patterns: [text]) -> bool:
    # Helper for runtime matching
    # ...
```

**Files to Modify:**
- `src/std/spec.spl` (+80 lines)

**Tests:**
```simple
describe "Condition Evaluation":
    it "returns false with no conditions":
        check(should_skip_test([], []) == false)

    it "matches current platform":
        check(should_skip_test(["linux"], []) == true)  # On Linux

    it "matches OR logic":
        check(should_skip_test(["windows"], ["interpreter"]) == true)  # On interpreter
```

**Deliverables:**
- `SkipCondition` struct with `matches()` method
- `should_skip_test()` evaluation function
- `matches_platform()` and `matches_runtime()` helpers
- 20+ unit tests

**Time Estimate:** 4 days

---

### Phase 3: Decorator Functions (Week 3) ⏳ NOT STARTED

#### Task 3.1: Skip Decorator

**Implementation:**
```simple
fn skip(
    platforms: [text] = [],
    runtimes: [text] = [],
    profiles: [text] = [],
    architectures: [text] = [],
    features: [text] = [],
    version: text = "",
    hardware: [text] = [],
    requires: [text] = [],
    env_vars: {text: text} = {},
    fs_features: [text] = [],
    network: bool = false,
    tags: [text] = [],
    reason: text = ""
) -> fn(text, fn()):
    """
    Create a skip decorator that skips tests based on ANY matching condition.

    Semantic: "Will implement in future" - This is a TODO item.
    Use when the feature SHOULD work in this environment but isn't implemented yet.

    Skipped tests are COUNTED in test totals and reported as "SKIP" to track technical debt.

    Usage Examples:
        # Platform-specific
        val skip_win = skip(platforms: ["windows"], reason: "Not yet ported")
        skip_win("file permissions test", fn(): chmod("/tmp/file", 0o644))

        # Runtime mode
        val skip_interp = skip(runtimes: ["interpreter"], reason: "Needs compiled mode")
        skip_interp("generic types test", fn(): val list = List<i32>())

        # Hardware requirements
        val skip_no_gpu = skip(hardware: ["gpu"], reason: "GPU-only test")
        skip_no_gpu("CUDA kernel test", fn(): launch_kernel())

        # Feature flags
        val skip_no_async = skip(features: ["async"], reason: "Async not impl")
        skip_no_async("async test", fn(): await fetch())

        # Multiple conditions (OR logic)
        val skip_complex = skip(
            platforms: ["windows"],
            runtimes: ["interpreter"],
            reason: "Needs Unix + compiled"
        )
        skip_complex("test", fn(): ...)
    """
    fn decorator(name: text, block: fn()):
        if should_skip_test(platforms, runtimes):
            val msg = if reason != "":
                "{reason} (platforms: {platforms.join(',')}, runtimes: {runtimes.join(',')})"
            else:
                "Skipped (platforms: {platforms.join(',')}, runtimes: {runtimes.join(',')})"
            skip_test(name, msg)
        else:
            it(name, block)

    decorator
```

**Helper Function:**
```simple
fn skip_test(name: text, reason: text):
    """Mark test as skipped with reason."""
    val indent = "  ".repeat(indent_level)
    print "{indent}  it {name} ... skipped ({reason})"
    test_skipped = test_skipped + 1
```

**Files to Modify:**
- `src/std/spec.spl` (+30 lines)

#### Task 3.2: Ignore Decorator

**Implementation:**
```simple
fn ignore(
    platforms: [text] = [],
    runtimes: [text] = [],
    profiles: [text] = [],
    architectures: [text] = [],
    features: [text] = [],
    version: text = "",
    hardware: [text] = [],
    requires: [text] = [],
    env_vars: {text: text} = {},
    fs_features: [text] = [],
    network: bool = false,
    tags: [text] = [],
    reason: text = ""
) -> fn(text, fn()):
    """
    Create an ignore decorator that completely ignores tests based on ANY matching condition.

    Semantic: "Fundamentally not supported" - This will NEVER be fixed.
    Use when the environment fundamentally lacks the capability.

    Ignored tests are NOT counted in test totals at all. Completely silent.

    Usage Examples:
        # Platform-specific API
        val ignore_win = ignore(platforms: ["windows"], reason: "Unix fork() API")
        ignore_win("fork test", fn(): pid = fork())

        # Architecture limitation
        val ignore_32bit = ignore(architectures: ["x86", "arm32"], reason: "64-bit only")
        ignore_32bit("large pointer test", fn(): ...)

        # Hardware requirement
        val ignore_no_gpu = ignore(hardware: ["gpu"], reason: "CUDA only, no CPU impl")
        ignore_no_gpu("GPU kernel test", fn(): ...)

        # Feature permanently disabled
        val ignore_no_jit = ignore(runtimes: ["interpreter"], reason: "JIT compilation only")
        ignore_no_jit("JIT optimization test", fn(): ...)

        # File system limitation
        val ignore_no_symlinks = ignore(
            fs_features: ["symlinks"],
            reason: "Symlinks not supported"
        )
        ignore_no_symlinks("symlink test", fn(): ...)
    """
    fn decorator(name: text, block: fn()):
        if should_skip_test(platforms, runtimes):
            # Completely silent - no output, no counting
            ()
        else:
            it(name, block)

    decorator
```

**Files to Modify:**
- `src/std/spec.spl` (+20 lines)

#### Task 3.3: only_on Decorator

**Implementation:**
```simple
fn only_on(platforms: [text] = [], runtimes: [text] = []) -> fn(text, fn()):
    """
    Create a decorator that runs tests ONLY on specified platforms/runtimes.
    Uses inverse logic of skip().

    Usage:
        val only_linux = only_on(platforms: ["linux"])
        only_linux("test name", fn(): test_body())
    """
    fn decorator(name: text, block: fn()):
        # Inverse logic: skip if NOT matching
        if not should_run_test(platforms, runtimes):
            skip_test(name, "Not on specified platform/runtime")
        else:
            it(name, block)

    decorator

fn should_run_test(platforms: [text], runtimes: [text]) -> bool:
    # Opposite of should_skip_test
    # Returns true if current env matches ANY condition
    should_skip_test(platforms, runtimes)
```

**Files to Modify:**
- `src/std/spec.spl` (+25 lines)

#### Task 3.4: skip_if Conditional Decorator

**Implementation:**
```simple
fn skip_if(condition: fn() -> bool, reason: text = "") -> fn(text, fn()):
    """
    Create a conditional skip decorator that evaluates a custom condition.

    Usage:
        val skip_no_ci = skip_if(fn(): env_get("CI") == nil, "Requires CI")
        skip_no_ci("test name", fn(): test_body())
    """
    fn decorator(name: text, block: fn()):
        if condition():
            val msg = if reason != "" then reason else "Condition not met"
            skip_test(name, msg)
        else:
            it(name, block)

    decorator
```

**Files to Modify:**
- `src/std/spec.spl` (+15 lines)

#### Task 3.5: Export New Functions

**Update exports:**
```simple
# Decorator functions (MUST actually skip, not just comments)
export skip, ignore, only_on, skip_if
```

**Deliverables:**
- 4 decorator functions fully implemented
- All functions exported from `std.spec`
- 30+ unit tests
- Usage examples documented

**Time Estimate:** 5 days

---

### Phase 4: Syntax Sugar (Week 4) ⏳ NOT STARTED

#### Task 4.1: Test Builder Pattern

**Implementation:**
```simple
struct TestBuilder:
    name: text
    block: fn()
    skip_platforms: [text]
    skip_runtimes: [text]
    skip_reason: text
    should_ignore: bool

    fn on_platforms(platforms: [text]) -> TestBuilder:
        TestBuilder(
            name: self.name,
            block: self.block,
            skip_platforms: platforms,
            skip_runtimes: self.skip_runtimes,
            skip_reason: self.skip_reason,
            should_ignore: self.should_ignore
        )

    fn on_runtimes(runtimes: [text]) -> TestBuilder:
        TestBuilder(
            name: self.name,
            block: self.block,
            skip_platforms: self.skip_platforms,
            skip_runtimes: runtimes,
            skip_reason: self.skip_reason,
            should_ignore: self.should_ignore
        )

    fn because(reason: text) -> TestBuilder:
        TestBuilder(
            name: self.name,
            block: self.block,
            skip_platforms: self.skip_platforms,
            skip_runtimes: self.skip_runtimes,
            skip_reason: reason,
            should_ignore: self.should_ignore
        )

    fn and_ignore() -> TestBuilder:
        TestBuilder(
            name: self.name,
            block: self.block,
            skip_platforms: self.skip_platforms,
            skip_runtimes: self.skip_runtimes,
            skip_reason: self.skip_reason,
            should_ignore: true
        )

    fn run():
        if should_skip_test(self.skip_platforms, self.skip_runtimes):
            if self.should_ignore:
                ()  # Complete ignore
            else:
                skip_test(self.name, self.skip_reason)
        else:
            it(self.name, self.block)

fn test(name: text) -> TestBuilder:
    """Create a test builder."""
    TestBuilder(
        name: name,
        block: fn(): (),  # Placeholder
        skip_platforms: [],
        skip_runtimes: [],
        skip_reason: "",
        should_ignore: false
    )

# Usage:
test("my test")
    .on_platforms(["windows"])
    .on_runtimes(["interpreter"])
    .because("Needs compiled mode on Unix")
    .run:
        test_body()
```

**Files to Create:**
- `src/std/spec/builder.spl` (NEW - ~120 lines)

**Deliverables:**
- `TestBuilder` struct with fluent API
- `test()` factory function
- 15+ unit tests
- Usage examples

**Time Estimate:** 3 days

#### Task 4.2: Documentation

**Documentation to Create:**
1. API Reference (`doc/api/spec_decorators.md`)
2. User Guide (`doc/guide/test_skip_ignore.md`)
3. Migration Guide (`doc/migration/skip_decorator_migration.md`)
4. Examples (`examples/testing/skip_ignore_examples.spl`)

**Time Estimate:** 2 days

---

### Phase 5: Parser Attributes (Future - Weeks 5-8) ⏳ FUTURE

**NOT IN CURRENT SCOPE** - Requires compiler changes

#### Task 5.1: Lexer Changes

**Add attribute token:**
```simple
# In lexer.spl
case "@":
    if self.peek().is_letter():
        # Parse attribute
        TokenKind.At
    else:
        # Error: @ must be followed by identifier
```

#### Task 5.2: Parser Changes

**Parse attribute syntax:**
```simple
# In parser.spl
fn parse_attributes() -> [Attribute]:
    # Parse: @skip(platforms=["windows"])
    # Parse: @ignore(runtimes=["interpreter"], reason="Not impl")
```

#### Task 5.3: Desugar Attributes

**Transform to function calls:**
```simple
# Source:
@skip(platforms=["windows"])
it "test":
    body()

# Desugared:
val __attr_0 = skip(platforms: ["windows"])
__attr_0("test", fn():
    body()
)
```

**Files to Modify:**
- `src/compiler/lexer.spl`
- `src/compiler/parser.spl`
- `src/compiler/desugar/attributes.spl` (NEW)

**Time Estimate:** 2-4 weeks (parser expertise required)

---

## Testing Strategy

### Unit Tests

**Location:** `test/lib/std/unit/spec/skip_decorator_spec.spl`

```simple
describe "Platform Detection":
    it "detects Linux":
        val info = get_platform_info()
        check(info.os == "linux")

    it "caches platform info":
        val info1 = get_platform_info()
        val info2 = get_platform_info()
        # Should be same object (cached)

describe "Skip Decorator":
    it "creates valid decorator":
        val decorator = skip(platforms: ["windows"])
        check(decorator != nil)

    it "skips on matching platform":
        var skipped = false
        val decorator = skip(platforms: ["linux"])  # Current platform
        decorator("test", fn():
            skipped = true
        )
        check(skipped == false)  # Should have been skipped
```

### Integration Tests

**Location:** `test/integration/skip_decorator_integration_spec.spl`

```simple
describe "End-to-End Skip":
    val skip_win = skip(platforms: ["windows"])

    skip_win("Windows-specific test", fn():
        # This should skip on Windows
        check(true)
    )

    # Verify skip count
    check(test_skipped > 0)
```

### Performance Tests

**Location:** `test/perf/skip_decorator_perf_spec.spl`

```simple
describe "Performance":
    it "platform detection is fast":
        val start = timestamp()
        for i in 0..1000:
            val info = get_platform_info()
        val elapsed = timestamp() - start
        check(elapsed < 10)  # < 10ms for 1000 calls (cached)

    it "condition evaluation is fast":
        val start = timestamp()
        for i in 0..10000:
            val result = should_skip_test(["windows"], ["interpreter"])
        val elapsed = timestamp() - start
        check(elapsed < 100)  # < 100ms for 10k evaluations
```

---

## Migration Guide

### Step 1: Identify Candidates

Find tests with manual platform checks:
```bash
grep -r "if is_windows\|if is_linux" test/ --include="*.spl"
```

### Step 2: Replace Manual Checks

**Before:**
```simple
it "Unix permissions":
    if is_windows():
        return  # Skip on Windows

    chmod("/tmp/file", 0o644)
    check(has_permissions())
```

**After:**
```simple
val skip_win = skip(platforms: ["windows"])
skip_win("Unix permissions", fn():
    chmod("/tmp/file", 0o644)
    check(has_permissions())
)
```

### Step 3: Replace Function-Based Skip

**Before:**
```simple
skip_on_windows("test name", fn():
    test_body()
)
```

**After:**
```simple
val skip_win = skip(platforms: ["windows"])
skip_win("test name", fn():
    test_body()
)
```

### Step 4: Add Runtime Conditions

**Before:**
```simple
skip_it "generic types":  # compiled-only
    val list = List<i32>()
```

**After:**
```simple
val compiled_only = skip(runtimes: ["interpreter"])
compiled_only("generic types", fn():
    val list = List<i32>()
)
```

---

## Success Metrics

| Metric | Target | Current |
|--------|--------|---------|
| Platform detection accuracy | 100% | 100% ✅ |
| Runtime detection accuracy | 100% | 0% ⏳ |
| Platform detection overhead | < 1ms | ~0.5ms ✅ |
| Decorator creation overhead | < 0.01ms | N/A |
| Tests using new syntax | 100+ | 0 |
| Documentation coverage | 100% | 0% |
| Unit test coverage | > 90% | 0% |

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Runtime detection hard | Medium | High | Use feature flags, env vars |
| Parser changes break tests | Low | High | Extensive testing, gradual rollout |
| Performance overhead | Low | Medium | Caching, optimization |
| API too complex | Medium | Medium | User testing, simplify if needed |
| Migration effort high | High | Medium | Provide tools, clear guide |

---

## Dependencies

**Required:**
- Platform detection ✅ DONE
- Runtime detection ⏳ TODO
- Test framework (spec.spl) ✅ EXISTS

**Optional:**
- Parser attribute support (Phase 5)
- Test result database
- CI integration

---

## Deliverables Checklist

### Phase 1: Foundation
- [ ] Runtime detection implemented
- [ ] `RuntimeInfo` struct created
- [ ] Caching layer complete
- [ ] Unit tests (15+)

### Phase 2: Core Logic
- [ ] `SkipCondition` struct
- [ ] `should_skip_test()` function
- [ ] Matching helpers
- [ ] Unit tests (20+)

### Phase 3: Decorators
- [ ] `skip()` function
- [ ] `ignore()` function
- [ ] `only_on()` function
- [ ] `skip_if()` function
- [ ] Exports updated
- [ ] Unit tests (30+)

### Phase 4: Syntax Sugar
- [ ] `TestBuilder` struct
- [ ] Builder methods
- [ ] Documentation complete
- [ ] Examples created

### Phase 5: Parser (Future)
- [ ] Lexer changes
- [ ] Parser changes
- [ ] Desugar pass
- [ ] Integration tests

---

## Timeline Summary

| Week | Phase | Status | Tasks |
|------|-------|--------|-------|
| 1-2 | Foundation | 25% | Platform ✅, Runtime, Architecture, Features |
| 3-4 | Detection | 0% | Hardware, Dependencies, Environment, File System, Network, Version |
| 5 | Core Logic | 0% | SkipCondition, comprehensive evaluator |
| 6 | Decorators | 0% | skip, ignore, only_on, skip_if |
| 7 | Syntax Sugar | 0% | TestBuilder, fluent API |
| 8 | Documentation | 0% | Docs, examples, migration guide |
| 9-12 | Parser (Future) | 0% | Attribute syntax |

**Total:** 8 weeks for comprehensive function-based system, +4 weeks for parser

---

## Next Steps

**Immediate (This Week):**
1. Complete runtime detection (Task 1.2)
2. Create `RuntimeInfo` struct
3. Write unit tests for detection

**Next Week:**
1. Implement `SkipCondition` struct
2. Implement condition evaluator
3. Write unit tests

**Week 3:**
1. Implement decorator functions
2. Update exports
3. Write integration tests

**Week 4:**
1. Implement TestBuilder
2. Write documentation
3. Create migration guide
4. Migrate 50+ tests as proof of concept

---

## Conclusion

This plan provides a clear, phased approach to implementing `@skip` and `@ignore` decorators. The function-based approach (Phases 1-4) can be completed in 4 weeks, providing immediate value. Parser attribute support (Phase 5) is a future enhancement that can be added later without breaking existing code.

**Key Benefits:**
- Multi-parameter skip/ignore support
- Clear skip vs ignore semantics
- Accurate platform/runtime detection
- Backward compatible
- Extensible architecture

**Start Date:** 2026-02-09 (suggested)
**Target Completion:** 2026-03-08 (4 weeks)
