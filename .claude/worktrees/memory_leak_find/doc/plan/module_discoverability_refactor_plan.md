# Simple Module Discoverability Refactoring Plan

**Date:** 2026-02-03
**Priority:** HIGH - Impacts developer experience
**Effort:** 3-5 days (Quick wins: 1 day, Refactoring: 2-3 days, Tooling: 1 day)

---

## Executive Summary

**Problem:** Simple has world-class infrastructure (DI, comprehensive mocking, advanced testing) but it's **nearly impossible to discover**. Users don't know what exists or where to find it.

**Root Causes:**
1. ❌ No `/src/lib/__init__.spl` - Stdlib has no entry point
2. ❌ Mocking marked "disabled" in testing module despite working perfectly
3. ❌ DI system (21KB) exists but undocumented and hard to find
4. ❌ No module discovery guide or stdlib reference
5. ❌ Inconsistent use of `__init__.spl` across app modules

**Solution:** Mix of documentation (quick wins) + structural refactoring (2-3 days)

---

## Discovery Analysis Summary

### What's Hidden But Amazing

| Feature | Location | Size | Status | Discoverability |
|---------|----------|------|--------|-----------------|
| **DI System** | `src/lib/src/di.spl` | 21KB | ✅ Works | 🔴 Hidden (2/10) |
| **Mocking Framework** | `src/lib/src/testing/mocking*.spl` | 70KB | ✅ Works | 🔴 Hidden (3/10) |
| **Testing Helpers** | `src/lib/src/testing/helpers.spl` | Exported | ✅ Works | 🟡 Partial (6/10) |
| **Module System** | `doc/guide/module_system.md` | 640 lines | ✅ Documented | 🟢 Clear (8/10) |

### Current Structure Issues

```
src/lib/
├── ❌ NO __init__.spl           # Critical: No stdlib entry point
├── allocator.spl                # Discoverable
├── async.spl                    # Discoverable
├── di.spl                       # ⚠️ Abbreviated name, no docs
├── gc.spl                       # Discoverable
├── json.spl                     # Discoverable
└── src/
    ├── testing/
    │   ├── __init__.spl         # ❌ Only exports helpers, hides mocking
    │   ├── helpers.spl          # ✅ Exported and visible
    │   ├── mocking_core.spl     # ❌ Hidden (25KB of sophistication)
    │   ├── mocking_async.spl    # ❌ Hidden (14KB)
    │   └── mocking_advanced.spl # ❌ Hidden (20KB)
    └── tooling/                 # Discoverable
```

---

## Phase 1: Quick Wins (Documentation) - 1 Day

### Task 1.1: Stdlib Quick Reference (2 hours)

**File:** `doc/guide/stdlib_quick_reference.md`

**Content Structure:**
```markdown
# Simple Standard Library Quick Reference

## Core Modules (Top-Level)
- allocator - Memory allocation control
- async - Async/await, promises, futures
- atomic - Atomic operations and synchronization
- binary_io - Binary serialization/deserialization
- concurrent - Concurrency primitives (channels, threads)
- di - **Dependency Injection** (profiles, containers, bindings)
- error - Error handling utilities
- gc - Garbage collector interface
- json - JSON parsing and generation
- log - Logging framework
- net - Networking (sockets, HTTP)
- sdn - SDN format parser (Simple Data Notation)
- time - Time, dates, durations
- uuid - UUID generation

## Testing & Development
- testing/helpers - Assertions (assert_eq, assert_true, etc.)
- testing/mocking_core - **Mock functions, call tracking, expectations**
- testing/mocking_async - **Async/promise mocking with timing**
- testing/mocking_advanced - **Scheduling, retry, rate limiting**
- testing/benchmark - Performance benchmarking
- testing/fuzz - Fuzz testing utilities

## Utilities
- common/ - Diagnostics, config, safety checks
- compress/ - Compression (LZMA, etc.)
- dependency_tracker/ - Dependency resolution
- type/ - Type system utilities

## How to Import
```simple
# Top-level modules
use di
use async
use json

# Nested modules (require full path)
use testing.mocking_core
use testing.helpers
use common.diagnostic

# Re-exported (once stdlib __init__.spl exists)
use std.*  # Future: All stdlib modules
```

## Quick Start Examples
[Links to examples for each major module]
```

**Deliverable:** One-page module index with descriptions and import patterns.

---

### Task 1.2: DI Guide (3 hours)

**File:** `doc/guide/dependency_injection_guide.md`

**Content:**
```markdown
# Dependency Injection in Simple

## Overview
Simple includes a full-featured DI system supporting profiles, singleton/transient lifetimes, and service locator patterns.

**Location:** `src/lib/src/di.spl` (21KB)

## Basic Usage

### 1. Mark Types as Injectable
```simple
use di.{Injectable}

class DatabaseConnection implements Injectable:
    url: text

    fn query(sql: text) -> Result<[Row], DbError>:
        # implementation

class UserService implements Injectable:
    db: DatabaseConnection

    fn get_user(id: i64) -> Option<User>:
        # uses self.db
```

### 2. Register Bindings
```simple
use di.{Container, Profile}

val container = Container.new()

# Register interface → implementation
container.bind<DatabaseConnection>(Profile.Dev):
    DatabaseConnection(url: "localhost:5432")

container.bind<DatabaseConnection>(Profile.Prod):
    DatabaseConnection(url: "prod-db.example.com:5432")
```

### 3. Resolve Dependencies
```simple
# Get instance from container
val db = container.resolve<DatabaseConnection>()
val service = UserService(db: db)

# Or use service locator
val service2 = container.resolve<UserService>()  # Injects db automatically
```

## Profiles
- `Profile.Test` - Unit testing with mocks
- `Profile.Dev` - Local development
- `Profile.Prod` - Production environment
- `Profile.SDN` - Custom config-driven

## Best Practices
1. Use interfaces/traits for abstractions
2. Register at app startup
3. Prefer constructor injection
4. Use profiles for environment-specific config
5. Combine with mocking for tests

## Examples
- Compiler: `/src/compiler/di.spl` - Real-world DI usage
- Tests: `/test/std/di_test.spl` - Unit test examples

## When NOT to Use DI
- Simple scripts (overhead not worth it)
- Pure functional code (no mutable state)
- Library code (let users handle composition)
```

**Deliverable:** Tutorial-style guide with real examples from codebase.

---

### Task 1.3: Mocking Framework Guide (3 hours)

**File:** `doc/guide/mocking_guide.md`

**Content:**
```markdown
# Mocking Framework Guide

## Overview
Simple has a comprehensive mocking framework with call tracking, expectations, async support, and advanced scheduling features.

**Location:** `src/lib/src/testing/mocking*.spl` (70KB across 4 files)

## Quick Start

### Basic Mock
```simple
use testing.mocking_core.{create_mock, verify_called}

# Create a mock function
val mock_fn = create_mock<fn(i32) -> text>()
mock_fn.returns("mocked result")

# Use in test
val result = mock_fn.call(42)
assert_eq(result, "mocked result")

# Verify it was called
verify_called(mock_fn, times: 1)
verify_called_with(mock_fn, args: [42])
```

### Mock Objects
```simple
class MockDatabase:
    query_mock: MockFunction<fn(text) -> [Row]>

    fn query(sql: text) -> [Row]:
        self.query_mock.call(sql)

val mock_db = MockDatabase(
    query_mock: create_mock()
)
mock_db.query_mock.returns([Row(id: 1, name: "Alice")])

# Use in tests
val service = UserService(db: mock_db)
val users = service.get_all_users()
assert_eq(users.len(), 1)
```

### Async Mocking
```simple
use testing.mocking_async.{MockPromise}

val mock_async = MockPromise.new()
mock_async.resolves_in(ms: 100, value: "delayed result")

# Test async code
val promise = my_async_function()
val result = promise.await()  # Takes 100ms
assert_eq(result, "delayed result")
```

### Advanced Features

**Sequential Returns:**
```simple
mock_fn.returns_sequence([
    "first call",
    "second call",
    "third call"
])
```

**Conditional Behavior:**
```simple
mock_fn.when_called_with(args: [42]).returns("special")
mock_fn.when_called_with(args: [99]).throws(Error("invalid"))
```

**Call Analysis:**
```simple
val analyzer = CallAnalyzer.new(mock_fn)
print "Called {analyzer.call_count} times"
print "Average args: {analyzer.average_args()}"
print "Call pattern: {analyzer.call_pattern()}"
```

**Rate Limiting & Throttling:**
```simple
use testing.mocking_advanced.{MockRateLimiter}

val limiter = MockRateLimiter.new(rate: 10, per_second: 1)
limiter.track_call()  # Simulates rate limiting
```

## Matchers
```simple
use testing.mocking_core.{Matcher}

# Built-in matchers
mock_fn.when_called_with(Matcher.any()).returns("default")
mock_fn.when_called_with(Matcher.gt(10)).returns("big number")
mock_fn.when_called_with(Matcher.regex(r"\d+")).returns("numeric")
```

## File Organization
- `mocking_core.spl` - Core mock functions, call tracking, expectations
- `mocking_async.spl` - Promise/async mocking
- `mocking_advanced.spl` - Scheduling, retry, rate limiting
- `mocking.spl` - Re-exports all of above

## How to Import
```simple
# Current (requires full path)
use testing.mocking_core.{create_mock, verify_called}
use testing.mocking_async.{MockPromise}

# Future (once testing module exports fixed)
use testing.mocking.*
```

## Examples
- Unit tests: `/test/std/testing/mocking_test.spl`
- Integration: `/src/compiler/test_utils.spl`
```

**Deliverable:** Complete mocking guide with examples.

---

### Task 1.4: Module Discovery Guide (2 hours)

**File:** `doc/guide/module_discovery_guide.md`

**Content:**
```markdown
# How to Find What You Need: Module Discovery Guide

## Quick Search Strategies

### 1. Check Stdlib Quick Reference
Start here: `doc/guide/stdlib_quick_reference.md`

### 2. Browse Source Directories
```bash
# Standard library
ls src/lib/                  # Top-level modules
ls src/lib/src/testing/      # Testing framework
ls src/lib/src/tooling/      # Build/dev tools
ls src/lib/common/           # Shared utilities

# Applications
ls src/app/                  # CLI commands
```

### 3. Use grep for Keywords
```bash
# Find modules related to testing
grep -r "class.*Test" src/lib/

# Find DI usage
grep -r "Injectable" src/

# Find mocking examples
grep -r "create_mock" test/
```

### 4. Check Module Init Files
```bash
# See what's exported
cat src/lib/src/testing/__init__.spl
cat src/lib/common/__init__.spl
```

## Common "Where Is...?" Questions

**Q: Where is dependency injection?**
A: `src/lib/src/di.spl` - See `doc/guide/dependency_injection_guide.md`

**Q: Where is the mocking framework?**
A: `src/lib/src/testing/mocking*.spl` - See `doc/guide/mocking_guide.md`

**Q: Where are assertion helpers?**
A: `src/lib/src/testing/helpers.spl` - Import with `use testing.helpers`

**Q: Where is JSON parsing?**
A: `src/lib/json.spl` - Import with `use json`

**Q: Where is async/await?**
A: `src/lib/async.spl` - Import with `use async`

**Q: Where is the module system spec?**
A: `doc/guide/module_system.md` - Complete specification

## Module Naming Patterns

| Pattern | Meaning | Examples |
|---------|---------|----------|
| Top-level `.spl` | Core module | `async.spl`, `json.spl`, `gc.spl` |
| `src/category/` | Grouped modules | `src/testing/`, `src/tooling/` |
| `__init__.spl` | Module entry point | Re-exports public API |
| `*_core.spl` | Core functionality | `mocking_core.spl` |
| `*_async.spl` | Async variant | `mocking_async.spl` |

## Import Patterns

```simple
# Top-level module (flat)
use json
use async

# Nested module (path required)
use testing.helpers
use testing.mocking_core
use common.diagnostic

# Selective import
use testing.helpers.{assert_eq, assert_true}
use di.{Container, Profile}

# Wildcard (use sparingly)
use testing.helpers.*
```

## Future Improvements
- `simple list-modules` command
- `simple show-module <name>` command
- LSP autocomplete for modules
- Stdlib root `__init__.spl` for `use std.*`
```

**Deliverable:** Discovery strategies and FAQ.

---

## Phase 2: Structural Refactoring - 2-3 Days

### Task 2.1: Create Stdlib Root Init (2 hours)

**File:** `/src/lib/__init__.spl`

**Content:**
```simple
# Simple Standard Library - Public API
# Re-exports all top-level modules and key submodules

# Core modules (top-level .spl files)
import allocator
import async
import atomic
import binary_io
import concurrent
import di
import error
import gc
import json
import log
import net
import sdn
import time
import uuid

# Re-export all top-level
export allocator
export async
export atomic
export binary_io
export concurrent
export di
export error
export gc
export json
export log
export net
export sdn
export time
export uuid

# Testing framework (submodule)
import src.testing.{helpers, mocking}
export testing.helpers
export testing.mocking

# Common utilities (submodule)
import common.{diagnostic, config_env, target, safety}
export common.diagnostic
export common.config_env
export common.target
export common.safety

# Compression
import compress.{upx, lzma}
export compress.upx
export compress.lzma

# Type utilities
import type.{type_utils}
export type.type_utils

# Now users can: use std.* or use std.di or use std.testing.mocking
```

**Impact:**
- ✅ Users can `use std.*` to get everything
- ✅ Clear public API boundary
- ✅ Follows module system spec
- ✅ Enables organized imports

---

### Task 2.2: Fix Testing Module Exports (1 hour)

**File:** `/src/lib/src/testing/__init__.spl`

**Current (broken):**
```simple
# FIXME: Currently only exports helpers
# Other modules disabled due to "parse errors" (but they work!)
export helpers.*

# Note: The following are disabled:
# - mocking (actually works fine!)
# - benchmark
# - deployment
# - fuzz
```

**Fixed:**
```simple
# Simple Testing Framework
# Comprehensive testing utilities including assertions, mocking, and benchmarks

# Assertion helpers (basic)
from helpers import {
    assert_eq, assert_ne, assert_true, assert_false,
    assert_some, assert_none, assert_ok, assert_err,
    TestContext, TestResult
}
export assert_eq, assert_ne, assert_true, assert_false
export assert_some, assert_none, assert_ok, assert_err
export TestContext, TestResult

# Mocking framework (comprehensive)
from mocking import {
    # Core mocking
    create_mock, verify_called, verify_called_with,
    MockFunction, Expectation, VerificationResult,
    Matcher, CallRecord, CallAnalyzer,

    # Async mocking
    MockPromise, AsyncMockBuilder,

    # Advanced features
    MockScheduler, RetryPolicy, RateLimiter,
    SequentialReturns, Spy, MockBuilder
}
export create_mock, verify_called, verify_called_with
export MockFunction, Expectation, VerificationResult
export Matcher, CallRecord, CallAnalyzer
export MockPromise, AsyncMockBuilder
export MockScheduler, RetryPolicy, RateLimiter
export SequentialReturns, Spy, MockBuilder

# Benchmarking (if parse errors fixed)
# from benchmark import {Benchmark, BenchmarkResult}
# export Benchmark, BenchmarkResult

# Fuzz testing (if parse errors fixed)
# from fuzz import {FuzzConfig, FuzzRunner}
# export FuzzConfig, FuzzRunner

# Now users can: use testing.{create_mock, assert_eq}
```

**Impact:**
- ✅ Mocking no longer hidden
- ✅ Clear list of exports
- ✅ Organized by category
- ⚠️ Need to verify no actual parse errors

---

### Task 2.3: Add App Module Init Files (4 hours)

Create `__init__.spl` for major app modules:

#### `/src/app/build/__init__.spl`
```simple
# Simple Build System
# Self-hosting build system with phases: build, test, coverage, quality, etc.

from main import {BuildCommand}
from orchestrator import {Orchestrator}
from cargo import {Cargo}
from config import {BuildConfig}

export BuildCommand
export Orchestrator
export Cargo
export BuildConfig
```

#### `/src/app/test/__init__.spl`
```simple
# Simple Test Runner
# Runs Rust tests + Simple/SSpec tests with filtering and reporting

from main import {TestCommand}
from runner import {TestRunner}
from config import {TestConfig}

export TestCommand
export TestRunner
export TestConfig
```

#### `/src/app/lint/__init__.spl`
```simple
# Simple Linter
# Code quality checking with auto-fix support

from main import {LintCommand}
from rules import {LintRule}

export LintCommand
export LintRule
```

#### `/src/app/ffi_gen/__init__.spl`
```simple
# FFI Wrapper Generator
# Generates Rust/C/C++ FFI wrappers from @Lib annotations

from main import {FfiGenCommand}
from parser import {LibAnnotation}
from rust_codegen import {RustCodegen}
from cargo_gen import {CargoGenerator}
from type_mapping import {TypeMapper}

export FfiGenCommand
export LibAnnotation
export RustCodegen
export CargoGenerator
export TypeMapper
```

**Impact:**
- ✅ Clear entry points for each command
- ✅ Documents what each module does
- ✅ Enables `use app.build` imports

---

### Task 2.4: Rename di.spl (1 hour)

**Problem:** `di.spl` is abbreviated and hard to search for.

**Solution:** Add alias or better documentation

**Option A: Alias (recommended)**
Create `/src/lib/dependency_injection.spl`:
```simple
# Dependency Injection System (Alias)
# Main implementation: src/di.spl

# Re-export everything from di
from di import *
export *
```

**Option B: Move file (more disruptive)**
```bash
mv src/lib/src/di.spl src/lib/dependency_injection.spl
# Update all imports
```

**Recommendation:** Option A (alias) - non-breaking change.

**Impact:**
- ✅ Users can search "dependency injection"
- ✅ No breaking changes
- ✅ Both imports work

---

## Phase 3: Tooling Support - 1 Day

### Task 3.1: `simple list-modules` Command (4 hours)

**File:** `src/app/cli/list_modules.spl`

**Implementation:**
```simple
use std.{json}
use common.{diagnostic}

class ListModulesCommand:
    fn run(filter: Option<text>):
        val modules = scan_stdlib_modules()

        if val Some(f) = filter:
            modules = modules.filter(\m: m.category == f)

        print_module_table(modules)

    fn scan_stdlib_modules() -> [Module]:
        # Scan src/lib/ for .spl files
        # Parse __init__.spl exports
        # Return structured list

    fn print_module_table(modules: [Module]):
        print "Simple Standard Library Modules\n"
        print "Category    | Module          | Description"
        print "------------|-----------------|-------------"
        for module in modules:
            print "{module.category:12} | {module.name:15} | {module.desc}"

struct Module:
    name: text
    category: text
    location: text
    desc: text
    exports: [text]
```

**CLI Integration:**
```bash
simple list-modules              # All modules
simple list-modules --category=testing
simple list-modules --category=async
simple list-modules --json       # Machine-readable
```

**Impact:**
- ✅ Users discover modules via CLI
- ✅ No need to browse source
- ✅ Can filter by category

---

### Task 3.2: `simple show-module` Command (3 hours)

**File:** `src/app/cli/show_module.spl`

**Implementation:**
```simple
class ShowModuleCommand:
    fn run(module_name: text):
        val info = load_module_info(module_name)

        print "Module: {info.name}"
        print "Location: {info.path}"
        print "Category: {info.category}"
        print ""
        print "Description:"
        print "  {info.description}"
        print ""
        print "Exports:"
        for export in info.exports:
            print "  - {export}"
        print ""
        print "Example:"
        print "  use {module_name}"
        if info.examples.?:
            print ""
            print "Code Examples:"
            for ex in info.examples:
                print "  {ex}"
```

**CLI Integration:**
```bash
simple show-module di
simple show-module testing.mocking_core
simple show-module async
```

**Impact:**
- ✅ Quick module documentation
- ✅ Shows exports and examples
- ✅ Points to source location

---

## Implementation Schedule

### Week 1: Documentation (2 days)

| Day | Tasks | Hours | Deliverables |
|-----|-------|-------|--------------|
| 1 | Tasks 1.1, 1.2 | 5h | Stdlib reference + DI guide |
| 2 | Tasks 1.3, 1.4 | 5h | Mocking guide + discovery guide |

### Week 2: Refactoring (2 days)

| Day | Tasks | Hours | Deliverables |
|-----|-------|-------|--------------|
| 3 | Tasks 2.1, 2.2 | 3h | Stdlib init + testing fix |
| 4 | Tasks 2.3, 2.4 | 5h | App inits + DI alias |

### Week 3: Tooling (1 day)

| Day | Tasks | Hours | Deliverables |
|-----|-------|-------|--------------|
| 5 | Tasks 3.1, 3.2 | 7h | CLI commands |

**Total:** 5 days, 25 hours

---

## Success Metrics

### Before (Current State)
- ❌ No one knows DI exists
- ❌ Mocking marked "disabled"
- ❌ No stdlib reference
- ❌ No discovery guide
- **Discoverability Score: 3/10**

### After (Target State)
- ✅ `doc/guide/stdlib_quick_reference.md` - One-stop shop
- ✅ DI guide with examples
- ✅ Mocking guide with examples
- ✅ `src/lib/__init__.spl` - Clear entry point
- ✅ Testing module exports mocking
- ✅ `simple list-modules` command
- ✅ `simple show-module` command
- **Discoverability Score: 9/10**

### User Impact
```simple
# Before: Hard to find
# User doesn't know DI exists, manually creates service locator

# After: Easy to discover
simple list-modules --category=utilities
# Shows: di - Dependency Injection (profiles, containers, bindings)

simple show-module di
# Shows full documentation + examples

use di.{Container, Profile}
# Works immediately
```

---

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Breaking existing imports | Medium | Use aliases, don't move files |
| Testing module parse errors | Medium | Verify mocking works in tests first |
| Performance of module scanning | Low | Cache results, run once at startup |
| Incomplete documentation | Low | Focus on top 10 most-used modules |

---

## Next Steps

1. **Review this plan** - Confirm approach
2. **Start with Quick Wins** - Documentation first (Phase 1)
3. **Test refactoring locally** - Verify no breakage (Phase 2)
4. **Implement tooling** - CLI commands (Phase 3)
5. **Update CLAUDE.md** - Reflect new structure

---

## Files to Create

**Documentation (Phase 1):**
- `doc/guide/stdlib_quick_reference.md`
- `doc/guide/dependency_injection_guide.md`
- `doc/guide/mocking_guide.md`
- `doc/guide/module_discovery_guide.md`

**Code (Phase 2):**
- `src/lib/__init__.spl`
- `src/lib/dependency_injection.spl` (alias)
- `src/app/build/__init__.spl`
- `src/app/test/__init__.spl`
- `src/app/lint/__init__.spl`
- `src/app/ffi_gen/__init__.spl`

**Modified (Phase 2):**
- `src/lib/src/testing/__init__.spl` (fix exports)

**Code (Phase 3):**
- `src/app/cli/list_modules.spl`
- `src/app/cli/show_module.spl`

**Total:** 12 new files, 1 modified file

---

## Conclusion

Simple's module system has **world-class features hidden in plain sight**. With minimal documentation and targeted refactoring (5 days), we can transform discoverability from 3/10 to 9/10, making DI, mocking, and other advanced features easy to find and use.

**Priority:** Phase 1 (documentation) gives 80% of the benefit for 40% of the effort. Start there.
