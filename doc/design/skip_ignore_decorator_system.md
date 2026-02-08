# @skip and @ignore Decorator System - Design Document

**Date:** 2026-02-08
**Status:** DESIGN PHASE
**Priority:** HIGH

## Executive Summary

Design a comprehensive decorator-based skip/ignore system that supports multiple platforms and runtimes in a single declaration:

```simple
@skip(platforms=["windows", "macos"], runtimes=["interpreter"])
it "advanced feature test":
    # This test is skipped on Windows, macOS, and in interpreter mode
    use_advanced_feature()

@ignore(platforms=["windows"], reason="Windows path handling differs")
it "Unix-specific path test":
    # This test is completely ignored on Windows (not even counted)
    check(path_separator() == "/")
```

## Requirements Analysis

### 1. Functional Requirements

**FR-1: Multi-Parameter Skip**
- Support multiple platforms: `platforms=["windows", "linux", "macos"]`
- Support multiple runtimes: `runtimes=["interpreter", "compiled", "jit"]`
- Support combination: `@skip(platforms=["windows"], runtimes=["interpreter"])`

**FR-2: Skip vs Ignore Semantics**
- `@skip`: Test is skipped, counted in "skipped" total
- `@ignore`: Test is ignored, NOT counted in test totals at all

**FR-3: Decorator Syntax**
- Must be parseable by runtime parser
- Should support named parameters
- Should support list parameters
- Optional reason parameter

**FR-4: Platform Detection**
- Detect: windows, linux, macos, unix, freebsd, openbsd, netbsd
- Runtime detection (not compile-time)

**FR-5: Runtime Detection**
- Detect: interpreter, compiled, jit
- Detect: debug, release
- Optional: detect specific features (generics, async, etc.)

### 2. Non-Functional Requirements

**NFR-1: Performance**
- Platform detection cached (computed once per test run)
- Minimal overhead for non-skipped tests

**NFR-2: Compatibility**
- Must work with existing `it`, `describe`, `context` functions
- Backward compatible with existing tests
- Can coexist with function-based skip (`skip_on_windows`, etc.)

**NFR-3: Usability**
- Clear error messages for invalid parameters
- IDE autocomplete support
- Self-documenting (reason parameter)

**NFR-4: Maintainability**
- Centralized platform/runtime detection
- Easy to add new platforms/runtimes
- Clear separation of concerns

## Architecture Design

### 1. Component Overview

```
┌─────────────────────────────────────────────────────────┐
│                   Test Decorator Layer                  │
│  @skip(...), @ignore(...), @only_on(...), @skip_if(...) │
└────────────────────┬────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────┐
│              Condition Evaluator                        │
│  evaluate_skip_conditions(platforms, runtimes, custom)  │
└────────────────────┬────────────────────────────────────┘
                     │
        ┌────────────┴────────────┐
        ▼                         ▼
┌──────────────────┐    ┌──────────────────┐
│ Platform Detector│    │ Runtime Detector │
│ - OS detection   │    │ - Mode detection │
│ - Arch detection │    │ - Feature detect │
└──────────────────┘    └──────────────────┘
        │                         │
        └────────────┬────────────┘
                     ▼
┌─────────────────────────────────────────────────────────┐
│                  Test Executor                          │
│         it(name, block) / skip_test(name, reason)       │
└─────────────────────────────────────────────────────────┘
```

### 2. Data Structures

**SkipCondition:**
```simple
struct SkipCondition:
    platforms: [text]      # List of platforms to skip on
    runtimes: [text]       # List of runtimes to skip on
    reason: text           # Why skip (documentation)
    ignore: bool           # true = ignore (not counted), false = skip (counted)
```

**PlatformInfo:**
```simple
struct PlatformInfo:
    os: text               # "windows", "linux", "macos", etc.
    arch: text             # "x86_64", "aarch64", etc.
    is_unix: bool          # true for Unix-like systems
```

**RuntimeInfo:**
```simple
struct RuntimeInfo:
    mode: text             # "interpreter", "compiled", "jit"
    build: text            # "debug", "release"
    has_generics: bool     # Feature flags
    has_async: bool
    has_jit: bool
```

### 3. API Design

**Decorator Functions:**
```simple
# Primary decorators
fn skip(platforms: [text] = [], runtimes: [text] = [], reason: text = "") -> fn(text, fn())
fn ignore(platforms: [text] = [], runtimes: [text] = [], reason: text = "") -> fn(text, fn())

# Convenience decorators
fn only_on(platforms: [text] = [], runtimes: [text] = []) -> fn(text, fn())
fn skip_if(condition: fn() -> bool, reason: text = "") -> fn(text, fn())

# Usage:
@skip(platforms=["windows"], reason="POSIX-only")
it "test name":
    test_body()
```

**Detection Functions:**
```simple
# Platform detection (cached)
fn get_platform_info() -> PlatformInfo
fn matches_platform(current: text, patterns: [text]) -> bool

# Runtime detection (cached)
fn get_runtime_info() -> RuntimeInfo
fn matches_runtime(current: text, patterns: [text]) -> bool

# Condition evaluation
fn should_skip(condition: SkipCondition) -> bool
fn should_ignore(condition: SkipCondition) -> bool
```

### 4. Decorator Syntax Support

**Option 1: Function-based (CURRENT CAPABILITY)**
```simple
# Works now - function that returns a function
fn with_skip(platforms: [text], runtimes: [text]) -> fn(text, fn()):
    fn decorator(name: text, block: fn()):
        if should_skip_test(platforms, runtimes):
            skip_test(name, "Platform/runtime skip")
        else:
            it(name, block)
    decorator

# Usage:
val skip_decorator = with_skip(["windows"], ["interpreter"])
skip_decorator("test name", fn():
    test_body()
)
```

**Option 2: Attribute-based (REQUIRES PARSER SUPPORT)**
```simple
# Ideal syntax - requires compiler decorator support
@skip(platforms=["windows"], runtimes=["interpreter"])
it "test name":
    test_body()

# Parser would transform to:
val __decorator_0 = skip(platforms=["windows"], runtimes=["interpreter"])
__decorator_0("test name", fn():
    test_body()
)
```

**Option 3: Trailing Block Syntax (HYBRID)**
```simple
# Works with current parser - trailing block syntax
skip(platforms: ["windows"], runtimes: ["interpreter"]).it "test name":
    test_body()

# Or with method chaining:
test("test name")
    .skip_on_platforms(["windows"])
    .skip_on_runtimes(["interpreter"])
    .run:
        test_body()
```

## Implementation Plan

### Phase 1: Foundation (Week 1)

**1.1 Platform Detection Enhancement**
- ✅ Already have: `is_windows()`, `is_linux()`, `is_macos()`, `is_unix()`
- Add: Architecture detection (`is_x86_64()`, `is_aarch64()`)
- Add: Caching layer for platform info
- Add: `PlatformInfo` struct with all detection results

**1.2 Runtime Detection**
- Implement: Mode detection (interpreter vs compiled)
- Implement: Build type detection (debug vs release)
- Implement: Feature detection (generics, async, jit available)
- Add: `RuntimeInfo` struct with all runtime info
- Add: Caching layer for runtime info

**Files to modify:**
- `src/std/spec.spl` - Add detection functions
- New file: `src/std/spec/platform.spl` - Platform detection
- New file: `src/std/spec/runtime.spl` - Runtime detection

### Phase 2: Core Skip/Ignore Logic (Week 2)

**2.1 SkipCondition Struct**
```simple
struct SkipCondition:
    platforms: [text]
    runtimes: [text]
    reason: text
    ignore: bool

    fn matches_current_env() -> bool:
        # Check if current platform/runtime matches conditions
```

**2.2 Condition Evaluator**
```simple
fn should_skip_test(platforms: [text], runtimes: [text]) -> bool:
    val platform_info = get_platform_info()
    val runtime_info = get_runtime_info()

    # Check platform match
    if platforms.len() > 0:
        if not matches_platform(platform_info.os, platforms):
            return false

    # Check runtime match
    if runtimes.len() > 0:
        if not matches_runtime(runtime_info.mode, runtimes):
            return false

    # If any condition matched, skip
    platforms.len() > 0 or runtimes.len() > 0
```

**Files to modify:**
- `src/std/spec.spl` - Add condition evaluation

### Phase 3: Decorator Implementation (Week 3)

**3.1 Function-Based Decorators**

```simple
# Skip decorator (counted as skipped)
fn skip(platforms: [text] = [], runtimes: [text] = [], reason: text = "") -> fn(text, fn()):
    fn decorator(name: text, block: fn()):
        if should_skip_test(platforms, runtimes):
            val msg = if reason != "" then reason else "Platform/runtime skip"
            skip_test(name, msg)
        else:
            it(name, block)
    decorator

# Ignore decorator (not counted at all)
fn ignore(platforms: [text] = [], runtimes: [text] = [], reason: text = "") -> fn(text, fn()):
    fn decorator(name: text, block: fn()):
        if should_skip_test(platforms, runtimes):
            # Don't even print anything - completely ignore
            ()
        else:
            it(name, block)
    decorator

# Only-on decorator (inverse logic)
fn only_on(platforms: [text] = [], runtimes: [text] = []) -> fn(text, fn()):
    fn decorator(name: text, block: fn()):
        if not should_skip_test(platforms, runtimes):
            skip_test(name, "Not on specified platform/runtime")
        else:
            it(name, block)
    decorator

# Conditional skip
fn skip_if(condition: fn() -> bool, reason: text = "") -> fn(text, fn()):
    fn decorator(name: text, block: fn()):
        if condition():
            skip_test(name, reason)
        else:
            it(name, block)
    decorator
```

**Files to modify:**
- `src/std/spec.spl` - Add decorator functions

### Phase 4: Syntax Sugar (Week 4)

**4.1 Method Chaining Builder**

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
        # Similar...

    fn because(reason: text) -> TestBuilder:
        # Similar...

    fn and_ignore() -> TestBuilder:
        # Similar...

    fn run():
        # Evaluate and run/skip test
        if should_skip_test(self.skip_platforms, self.skip_runtimes):
            if self.should_ignore:
                ()  # Complete ignore
            else:
                skip_test(self.name, self.skip_reason)
        else:
            it(self.name, self.block)

# Usage:
test("my test")
    .on_platforms(["windows", "macos"])
    .on_runtimes(["interpreter"])
    .because("Requires compiled mode")
    .run:
        test_body()
```

**Files to create:**
- `src/std/spec/builder.spl` - Test builder pattern

### Phase 5: Attribute Syntax (Future - Parser Enhancement)

**5.1 Parser Changes**
- Modify lexer to recognize `@identifier` as attribute token
- Modify parser to parse attribute lists before function/test definitions
- Desugar attributes to function calls

**5.2 Syntax Transformation**
```simple
# Source code:
@skip(platforms=["windows"])
it "test":
    body()

# Desugared to:
val __attr_0 = skip(platforms: ["windows"])
__attr_0("test", fn():
    body()
)
```

**Files to modify:**
- `src/compiler/lexer.spl` - Add attribute token
- `src/compiler/parser.spl` - Add attribute parsing
- `src/compiler/desugar/` - Add attribute desugaring

## Usage Examples

### Example 1: Platform-Specific Skip

```simple
use std.spec.{describe, skip}

describe "File System Tests":
    # Skip on Windows and macOS (Unix-only test)
    val unix_only = skip(platforms: ["windows", "macos"])
    unix_only("symlink creation", fn():
        create_symlink("/tmp/link", "/tmp/target")
        check(symlink_exists("/tmp/link"))
    )

    # Or with reason:
    val skip_win = skip(
        platforms: ["windows"],
        reason: "Windows uses different permission model"
    )
    skip_win("chmod permissions", fn():
        chmod("/tmp/file", 0o644)
        check(has_permissions("/tmp/file", 0o644))
    )
```

### Example 2: Runtime-Specific Skip

```simple
describe "Advanced Features":
    # Skip in interpreter (compiled-only)
    val compiled_only = skip(runtimes: ["interpreter"])
    compiled_only("generic types", fn():
        val list = List<i32>()
        check(list.len() == 0)
    )

    # Skip in JIT mode
    val no_jit = skip(runtimes: ["jit"])
    no_jit("static analysis", fn():
        val result = analyze_statically()
        check(result.is_sound())
    )
```

### Example 3: Combined Conditions

```simple
describe "Complex Skip Conditions":
    # Skip on Windows in interpreter mode
    val skip_both = skip(
        platforms: ["windows"],
        runtimes: ["interpreter"],
        reason: "Requires compiled Windows build"
    )
    skip_both("Windows API test", fn():
        call_windows_api()
    )
```

### Example 4: Ignore (Not Counted)

```simple
describe "Experimental Features":
    # Completely ignore (not even counted in totals)
    val ignore_unstable = ignore(
        platforms: ["windows", "macos"],
        reason: "Only tested on Linux currently"
    )
    ignore_unstable("experimental algorithm", fn():
        test_experimental_feature()
    )
```

### Example 5: Conditional Skip

```simple
describe "Environment-Dependent Tests":
    # Skip if environment variable not set
    val skip_no_env = skip_if(
        condition: fn(): env_get("CI") == nil,
        reason: "Requires CI environment"
    )
    skip_no_env("CI-only test", fn():
        run_ci_specific_test()
    )
```

## Migration Strategy

### Phase 1: Add New Functions (Backward Compatible)

1. Add new decorator functions to `std.spec`
2. Export alongside existing skip functions
3. Document both approaches
4. Existing tests continue working

### Phase 2: Migrate High-Value Tests

1. Identify tests with multiple platform checks
2. Migrate to decorator syntax
3. Verify behavior identical
4. Update documentation

### Phase 3: Deprecate Old Syntax (Optional)

1. Mark old functions as deprecated
2. Add warnings for old syntax
3. Provide migration guide
4. Eventually remove (major version bump)

## Testing Strategy

### Unit Tests

```simple
describe "Platform Detection":
    it "detects current platform":
        val info = get_platform_info()
        check(info.os.len() > 0)

    it "caches platform info":
        val info1 = get_platform_info()
        val info2 = get_platform_info()
        check(info1.os == info2.os)

describe "Skip Condition Evaluation":
    it "skips on matching platform":
        val should = should_skip_test(["linux"], [])
        # Result depends on current platform

describe "Decorator Functions":
    it "creates valid decorator":
        val decorator = skip(platforms: ["windows"])
        check(decorator != nil)
```

### Integration Tests

```simple
describe "End-to-End Skip":
    val skip_win = skip(platforms: ["windows"])
    skip_win("this should skip on Windows", fn():
        check(true)
    )

    # Verify skip count updated correctly
    check(test_skipped > 0)
```

## Performance Considerations

### Caching Strategy

```simple
# Platform detection cached at module load
var _cached_platform_info = nil

fn get_platform_info() -> PlatformInfo:
    if _cached_platform_info == nil:
        _cached_platform_info = detect_platform()
    _cached_platform_info
```

### Benchmark Targets

- Platform detection: < 1ms (cached: < 0.001ms)
- Condition evaluation: < 0.1ms
- Decorator creation: < 0.01ms
- Total overhead per test: < 0.2ms

## Error Handling

### Invalid Parameters

```simple
fn skip(platforms: [text] = [], runtimes: [text] = [], reason: text = ""):
    # Validate platforms
    val valid_platforms = ["windows", "linux", "macos", "unix", "freebsd", "openbsd", "netbsd"]
    for platform in platforms:
        if not valid_platforms.contains(platform):
            print "Warning: Unknown platform '{platform}'"

    # Validate runtimes
    val valid_runtimes = ["interpreter", "compiled", "jit", "debug", "release"]
    for runtime in runtimes:
        if not valid_runtimes.contains(runtime):
            print "Warning: Unknown runtime '{runtime}'"

    # Return decorator
    # ...
```

### Error Messages

- Unknown platform: "Warning: Unknown platform 'xyz'. Valid: windows, linux, macos, ..."
- Unknown runtime: "Warning: Unknown runtime 'xyz'. Valid: interpreter, compiled, jit, ..."
- No conditions: "Warning: skip() with no conditions will never skip"

## Documentation Requirements

### API Documentation

1. Function signatures with examples
2. Parameter descriptions
3. Platform/runtime value lists
4. Migration guide from old syntax

### User Guide

1. Quick start examples
2. Common patterns
3. Best practices
4. Troubleshooting

### Internal Documentation

1. Architecture decisions
2. Caching strategy
3. Parser integration points
4. Future enhancement roadmap

## Future Enhancements

### Phase 6: Advanced Features

1. **Architecture-specific skip:**
   ```simple
   @skip(architectures=["arm32", "mips"])
   ```

2. **Version-specific skip:**
   ```simple
   @skip(min_version="1.5.0", max_version="2.0.0")
   ```

3. **Feature-specific skip:**
   ```simple
   @skip(requires_features=["async", "generics"])
   ```

4. **Custom conditions:**
   ```simple
   @skip_if(fn(): !has_gpu())
   ```

5. **Skip groups:**
   ```simple
   @skip_group("slow_tests")
   @skip_group("integration_tests")
   ```

## Success Criteria

1. ✅ All decorator functions implemented and tested
2. ✅ Platform/runtime detection working accurately
3. ✅ Performance overhead < 0.2ms per test
4. ✅ Backward compatible with existing tests
5. ✅ Documentation complete
6. ✅ Migration guide available
7. ✅ 100+ tests migrated successfully

## Timeline

| Phase | Duration | Deliverables |
|-------|----------|-------------|
| Phase 1 | Week 1 | Platform/runtime detection |
| Phase 2 | Week 2 | Core skip/ignore logic |
| Phase 3 | Week 3 | Decorator functions |
| Phase 4 | Week 4 | Syntax sugar/builders |
| Phase 5 | Future | Parser attribute support |

**Total:** 4 weeks for function-based implementation
**Extended:** +2-4 weeks for parser attribute support

## Conclusion

This design provides a comprehensive, extensible skip/ignore system that:
- Supports multiple platforms and runtimes
- Provides both skip (counted) and ignore (not counted) semantics
- Maintains backward compatibility
- Offers clear migration path
- Enables future enhancements

The phased approach allows incremental delivery of value while building toward the ideal syntax.
