# Critical Issue: Test Framework Missing

## Problem

**174+ test files cannot run** because they import `std.spec` or `sspec` which doesn't exist in the source code.

## Symptoms

```
Error: parse error: Unexpected token: expected Fn, found Identifier { name: "describe", pattern: Immutable }
```

## Root Cause

Test files import non-existent modules:
```simple
use std.spec          # Module doesn't exist
use sspec             # Module doesn't exist
```

Tests expect these functions:
- `describe(name, block)` - Test suite definition
- `it(name, block)` - Individual test
- `expect(value)` - Assertion helper  
- `assert(condition)` - Basic assertion
- `assert_eq(a, b)` - Equality assertion

## Affected Files

6 parse errors from missing `describe`:
- `test/baremetal/arm32_boot_spec.spl`
- `test/baremetal/arm64_boot_spec.spl`
- `test/baremetal/riscv64_boot_spec.spl`
- `test/baremetal/x86_64_boot_spec.spl`
- `test/baremetal/x86_boot_spec.spl`
- (1 more file)

**Estimated total**: 100-200+ test files using sspec framework

## Analysis

### What Tests Expect

```simple
use sspec (describe, it, expect, assert, assert_eq)

describe "Feature Name":
    it "does something":
        val result = compute()
        expect result == 42
        assert result > 0
```

### What's Actually Available

The runtime provides `rt_cli_run_tests()` but no spec framework in Simple source.

## Solutions

### Option 1: Implement Minimal sspec (RECOMMENDED)

Create `src/std/spec.spl`:
```simple
# Minimal SSpec implementation
fn describe(name: text, block: fn()):
    print "describe {name}"
    block()

fn it(name: text, block: fn()):
    print "  it {name}"
    try:
        block()
        print "    ✓ pass"
    catch e:
        print "    ✗ fail: {e}"

fn expect(value):
    ExpectHelper(value: value)

struct ExpectHelper:
    value: any
    
    fn to_equal(expected):
        if self.value != expected:
            throw "Expected {expected}, got {self.value}"
    
    fn to_be(expected):
        if self.value != expected:
            throw "Expected {expected}, got {self.value}"

fn assert(condition: bool):
    if not condition:
        throw "Assertion failed"

fn assert_eq(a, b):
    if a != b:
        throw "Expected {b}, got {a}"

export describe, it, expect, assert, assert_eq
```

**Effort**: 2-4 hours
**Impact**: Fixes 100-200 test files

### Option 2: Convert Tests to Runtime Format

Convert tests to use `rt_cli_run_tests()` directly.

**Effort**: 20-40 hours  
**Impact**: Major test refactor

### Option 3: Skip sspec Tests

Mark all sspec tests as skipped/ignored.

**Effort**: 30 minutes
**Impact**: Reduces test coverage significantly

## Recommendation

**Implement Option 1** - Create minimal sspec framework.

This is the quickest path to getting 100-200 additional tests running and provides immediate value.

## Related Issues

- Assert keyword bug (already fixed, needs rebuild)
- Missing test framework is separate from assert function
- Runtime has test execution but no Simple-side framework

## Priority

**HIGH** - Blocking 100-200 test files from running.

This is more impactful than any other remaining fix.
