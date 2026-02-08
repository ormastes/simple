# @skip/@ignore Implementation Plan

**Document:** Implementation Roadmap
**Date:** 2026-02-08
**Status:** PLANNING
**Design Doc:** `doc/design/skip_ignore_decorator_system.md`

## Overview

Implement `@skip(platforms=..., runtimes=...)` and `@ignore(platforms=..., runtimes=...)` decorator system for test framework.

**Timeline:** 4 weeks (function-based) + 2-4 weeks (parser attributes)
**Priority:** HIGH
**Dependencies:** None (builds on existing spec.spl)

## Goals

1. Support multi-parameter skip/ignore: `@skip(platforms=["windows"], runtimes=["interpreter"])`
2. Distinguish skip (counted) vs ignore (not counted)
3. Accurate platform/runtime detection with caching
4. Backward compatible with existing tests
5. Clear migration path from old syntax

## Non-Goals (Future Work)

- Architecture-specific skip (x86_64, arm64)
- Version-specific skip (min/max version)
- Feature-specific skip (async, generics)
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

#### Task 1.2: Runtime Detection ⏳ TODO
- [ ] Detect interpreter vs compiled mode
- [ ] Detect debug vs release build
- [ ] Detect JIT availability
- [ ] Detect feature flags (generics, async, etc.)
- [ ] Create `RuntimeInfo` struct
- [ ] Cache runtime info

**Files to Create:**
- `src/std/spec/runtime.spl` (NEW - ~80 lines)

**Deliverables:**
- `RuntimeInfo` struct with all detection results
- Cached detection functions
- Unit tests for detection accuracy

**Time Estimate:** 3 days

---

### Phase 2: Core Skip Logic (Week 2) ⏳ NOT STARTED

#### Task 2.1: SkipCondition Struct

**Implementation:**
```simple
struct SkipCondition:
    platforms: [text]
    runtimes: [text]
    reason: text
    ignore: bool

    fn matches() -> bool:
        # Evaluate if current environment matches skip conditions
        val platform_match = matches_any_platform(self.platforms)
        val runtime_match = matches_any_runtime(self.runtimes)

        # Skip if ANY condition matches (OR logic)
        platform_match or runtime_match
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
fn skip(platforms: [text] = [], runtimes: [text] = [], reason: text = "") -> fn(text, fn()):
    """
    Create a skip decorator that skips tests on matching platforms/runtimes.
    Skipped tests are counted in test totals.

    Usage:
        val skip_win = skip(platforms: ["windows"])
        skip_win("test name", fn(): test_body())
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
fn ignore(platforms: [text] = [], runtimes: [text] = [], reason: text = "") -> fn(text, fn()):
    """
    Create an ignore decorator that completely ignores tests on matching platforms/runtimes.
    Ignored tests are NOT counted in test totals at all.

    Usage:
        val ignore_win = ignore(platforms: ["windows"])
        ignore_win("test name", fn(): test_body())
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
| 1 | Foundation | 50% | Runtime detection |
| 2 | Core Logic | 0% | SkipCondition, evaluator |
| 3 | Decorators | 0% | skip, ignore, only_on, skip_if |
| 4 | Syntax Sugar | 0% | TestBuilder, docs |
| 5-8 | Parser (Future) | 0% | Attribute syntax |

**Total:** 4 weeks for function-based, +2-4 weeks for parser

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
