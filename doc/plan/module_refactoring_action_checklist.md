# Module Discoverability - Action Checklist

**Goal:** Improve Simple module discoverability from 4.1/10 to 9.0/10
**Effort:** 5 days (25 hours)
**Priority:** HIGH - Developer experience critical

---

## Quick Start: Phase 1 Only (Recommended)

**If you only have 1 day:**
✅ Complete Phase 1 (documentation) for 80% of benefit

---

## Phase 1: Documentation (Day 1-2) 🎯 START HERE

### ✅ Task 1.1: Create Stdlib Quick Reference (2 hours)

**File:** `doc/guide/stdlib_quick_reference.md`

```bash
# Create the file
touch doc/guide/stdlib_quick_reference.md

# Content outline:
# - Core modules list (allocator, async, di, json, etc.)
# - Testing & development modules
# - Utilities (common, compress, type)
# - Import examples
# - Quick start examples
```

**Checklist:**
- [ ] List all 14 top-level stdlib modules
- [ ] Describe each module (1 line)
- [ ] Show import patterns
- [ ] Add links to examples
- [ ] Cross-reference with module_system.md

**Validation:**
```bash
# Check file exists and is readable
cat doc/guide/stdlib_quick_reference.md | head -20
```

---

### ✅ Task 1.2: Create DI Guide (3 hours)

**File:** `doc/guide/dependency_injection_guide.md`

```bash
# Create the file
touch doc/guide/dependency_injection_guide.md

# Reference implementation:
cat src/std/src/di.spl  # 21KB source

# Reference usage:
grep -r "Injectable" src/compiler/  # Real examples
```

**Checklist:**
- [ ] Overview section (what is DI?)
- [ ] Basic usage example
- [ ] Container API
- [ ] Profile system (Test, Dev, Prod, SDN)
- [ ] Best practices
- [ ] Real-world examples from codebase
- [ ] When NOT to use DI

**Validation:**
```bash
# Verify examples work
simple test doc/guide/dependency_injection_guide.md  # If examples are code
```

---

### ✅ Task 1.3: Create Mocking Guide (3 hours)

**File:** `doc/guide/mocking_guide.md`

```bash
# Create the file
touch doc/guide/mocking_guide.md

# Reference implementation:
cat src/std/src/testing/mocking_core.spl      # 25KB
cat src/std/src/testing/mocking_async.spl     # 14KB
cat src/std/src/testing/mocking_advanced.spl  # 20KB
cat src/std/src/testing/mocking.spl           # Aggregator

# Reference usage:
grep -r "create_mock" test/  # Real test examples
```

**Checklist:**
- [ ] Quick start (basic mock)
- [ ] Mock objects
- [ ] Async mocking
- [ ] Advanced features (sequential returns, matchers)
- [ ] Call analysis
- [ ] Rate limiting & throttling
- [ ] File organization explanation
- [ ] Import patterns (current vs future)

**Validation:**
```bash
# Test examples compile
simple test test/std/testing/mocking_test.spl
```

---

### ✅ Task 1.4: Create Discovery Guide (2 hours)

**File:** `doc/guide/module_discovery_guide.md`

```bash
# Create the file
touch doc/guide/module_discovery_guide.md

# Content outline:
# - Quick search strategies
# - Common "Where is...?" FAQ
# - Module naming patterns
# - Import patterns
# - Future improvements
```

**Checklist:**
- [ ] Search strategies (grep, ls, init files)
- [ ] FAQ (Where is DI? Where is mocking? etc.)
- [ ] Naming pattern guide
- [ ] Import pattern examples
- [ ] Links to other guides

**Validation:**
```bash
# Verify all referenced files exist
grep -o "src/[^)]*" doc/guide/module_discovery_guide.md | xargs -I {} ls {}
```

---

### 🎯 Phase 1 Complete Checkpoint

**After Phase 1, users can:**
- ✅ Find all stdlib modules via quick reference
- ✅ Learn DI with guide + examples
- ✅ Learn mocking with guide + examples
- ✅ Discover features via strategies

**Discoverability:** 4.1/10 → 7.5/10 (+83%)

**Commit:**
```bash
jj describe -m "docs: Add module discovery guides (DI, mocking, stdlib reference)

- Add stdlib quick reference (all 14 modules + submodules)
- Add DI guide with examples from compiler
- Add mocking guide (70KB of hidden features revealed)
- Add module discovery guide (search strategies + FAQ)

Improves discoverability from 4.1/10 to 7.5/10"

jj bookmark set main -r @
jj git push --bookmark main
```

---

## Phase 2: Structural Refactoring (Day 3-4)

### ✅ Task 2.1: Create Stdlib Root Init (2 hours)

**File:** `src/std/__init__.spl`

```bash
# Create the file
touch src/std/__init__.spl
```

**Checklist:**
- [ ] Import all 14 top-level modules
- [ ] Export all top-level modules
- [ ] Import key submodules (testing, common, compress, type)
- [ ] Export submodules
- [ ] Add module documentation comment

**Template:**
```simple
# Simple Standard Library - Public API

# Core modules
import allocator
import async
import atomic
# ... (all 14)

export allocator
export async
# ... (all 14)

# Submodules
import src.testing.{helpers, mocking}
export testing.helpers
export testing.mocking
```

**Validation:**
```bash
# Test import works
echo "use std.*" | simple --eval
echo "use std.{di, async, json}" | simple --eval
```

---

### ✅ Task 2.2: Fix Testing Module Exports (1 hour)

**File:** `src/std/src/testing/__init__.spl`

```bash
# Backup original
cp src/std/src/testing/__init__.spl src/std/src/testing/__init__.spl.bak

# Edit file
# Replace "export helpers.*" with explicit exports
# Add mocking exports
```

**Checklist:**
- [ ] Export helpers (assert_eq, assert_true, etc.)
- [ ] Export mocking (create_mock, verify_called, etc.)
- [ ] Export async mocking (MockPromise, etc.)
- [ ] Export advanced mocking (MockScheduler, etc.)
- [ ] Remove "disabled" comment
- [ ] Add documentation comment

**Validation:**
```bash
# Test mocking is now visible
echo "use testing.mocking.{create_mock}" | simple --eval

# Run mocking tests
simple test test/std/testing/mocking_test.spl
```

---

### ✅ Task 2.3: Add App Module Init Files (4 hours)

**Files:**
- `src/app/build/__init__.spl`
- `src/app/test/__init__.spl`
- `src/app/lint/__init__.spl`
- `src/app/ffi_gen/__init__.spl`

```bash
# Create all init files
touch src/app/build/__init__.spl
touch src/app/test/__init__.spl
touch src/app/lint/__init__.spl
touch src/app/ffi_gen/__init__.spl
```

**For each file:**
- [ ] Import main command class
- [ ] Import key utilities
- [ ] Export all imports
- [ ] Add module documentation

**Validation:**
```bash
# Test imports work
echo "use app.build.{BuildCommand}" | simple --eval
echo "use app.ffi_gen.{FfiGenCommand}" | simple --eval
```

---

### ✅ Task 2.4: Create DI Alias (1 hour)

**File:** `src/std/dependency_injection.spl`

```bash
# Create alias file
touch src/std/dependency_injection.spl
```

**Content:**
```simple
# Dependency Injection System (Alias)
# Main implementation: src/di.spl
# This alias makes the module easier to discover

from di import *
export *
```

**Checklist:**
- [ ] Re-export all from di
- [ ] Add documentation comment
- [ ] Explain alias purpose

**Validation:**
```bash
# Test both imports work
echo "use di" | simple --eval
echo "use dependency_injection" | simple --eval
```

---

### 🎯 Phase 2 Complete Checkpoint

**After Phase 2, users can:**
- ✅ Import `use std.*` for everything
- ✅ Import mocking from testing module
- ✅ Import app modules with clear names
- ✅ Search for "dependency injection" and find it

**Discoverability:** 7.5/10 → 8.5/10 (+13%)

**Commit:**
```bash
jj describe -m "refactor: Add module init files for discoverability

- Add src/std/__init__.spl (stdlib entry point)
- Fix src/std/src/testing/__init__.spl (export mocking)
- Add app module init files (build, test, lint, ffi_gen)
- Add dependency_injection.spl alias for di.spl

Improves discoverability from 7.5/10 to 8.5/10
No breaking changes - all existing imports still work"

jj bookmark set main -r @
jj git push --bookmark main
```

---

## Phase 3: Tooling Support (Day 5)

### ✅ Task 3.1: Implement `list-modules` Command (4 hours)

**File:** `src/app/cli/list_modules.spl`

```bash
# Create file
touch src/app/cli/list_modules.spl
```

**Implementation checklist:**
- [ ] Scan `src/std/` for .spl files
- [ ] Parse `__init__.spl` files for exports
- [ ] Categorize modules (core, testing, utilities)
- [ ] Format as table
- [ ] Add --category filter
- [ ] Add --json output option

**Integration:**
- [ ] Add to `src/app/cli/main.spl` command dispatch
- [ ] Add to `simple --help` output

**Validation:**
```bash
# Test command
simple list-modules
simple list-modules --category=testing
simple list-modules --json | jq .
```

---

### ✅ Task 3.2: Implement `show-module` Command (3 hours)

**File:** `src/app/cli/show_module.spl`

```bash
# Create file
touch src/app/cli/show_module.spl
```

**Implementation checklist:**
- [ ] Load module info (location, exports)
- [ ] Extract documentation comments
- [ ] Format output (name, location, category, description)
- [ ] Show exports list
- [ ] Show example usage
- [ ] Link to guide docs if available

**Integration:**
- [ ] Add to `src/app/cli/main.spl` command dispatch

**Validation:**
```bash
# Test command
simple show-module di
simple show-module testing.mocking_core
simple show-module async
```

---

### 🎯 Phase 3 Complete Checkpoint

**After Phase 3, users can:**
- ✅ Discover modules via CLI without leaving terminal
- ✅ See all available modules with `list-modules`
- ✅ Inspect any module with `show-module`
- ✅ Filter modules by category

**Discoverability:** 8.5/10 → 9.0/10 (+6%)

**Commit:**
```bash
jj describe -m "feat: Add module discovery CLI commands

- Add 'simple list-modules' command (filter by category)
- Add 'simple show-module <name>' command (detailed info)
- Enables terminal-based module discovery

Improves discoverability from 8.5/10 to 9.0/10"

jj bookmark set main -r @
jj git push --bookmark main
```

---

## Final Validation

### End-to-End Test

```bash
# 1. Documentation exists
ls doc/guide/stdlib_quick_reference.md
ls doc/guide/dependency_injection_guide.md
ls doc/guide/mocking_guide.md
ls doc/guide/module_discovery_guide.md

# 2. Stdlib init exists
ls src/std/__init__.spl

# 3. Testing exports mocking
grep "export.*create_mock" src/std/src/testing/__init__.spl

# 4. App inits exist
ls src/app/build/__init__.spl
ls src/app/test/__init__.spl
ls src/app/lint/__init__.spl
ls src/app/ffi_gen/__init__.spl

# 5. DI alias exists
ls src/std/dependency_injection.spl

# 6. CLI commands work
simple list-modules
simple show-module di

# 7. Imports work
simple --eval "use std.*"
simple --eval "use testing.mocking.{create_mock}"
simple --eval "use dependency_injection as di"

# 8. Tests pass
simple test
```

### User Acceptance Test

**Scenario: New user discovers DI**

```bash
# Step 1: User searches for modules
$ simple list-modules | grep -i depend
core         | di                      | Dependency Injection
core         | dependency_injection    | Dependency Injection (alias)

# Step 2: User inspects module
$ simple show-module di
Module: di
Location: src/std/src/di.spl
Category: core
Description: Dependency Injection with profiles, containers, bindings
...

# Step 3: User reads guide
$ cat doc/guide/dependency_injection_guide.md
# Comprehensive tutorial with examples

# Step 4: User uses DI
$ cat > test_di.spl << 'EOF'
use di.{Container, Profile}

val container = Container.new()
print "DI works!"
EOF

$ simple test_di.spl
DI works!
```

**Result:** ✅ User discovers DI in <5 minutes (previously: never)

---

## Progress Tracking

### Overall Progress

- [ ] Phase 1: Documentation (8 hours)
  - [ ] Task 1.1: Stdlib Quick Reference (2h)
  - [ ] Task 1.2: DI Guide (3h)
  - [ ] Task 1.3: Mocking Guide (3h)
  - [ ] Task 1.4: Discovery Guide (2h)

- [ ] Phase 2: Refactoring (8 hours)
  - [ ] Task 2.1: Stdlib Root Init (2h)
  - [ ] Task 2.2: Fix Testing Exports (1h)
  - [ ] Task 2.3: App Module Inits (4h)
  - [ ] Task 2.4: DI Alias (1h)

- [ ] Phase 3: Tooling (7 hours)
  - [ ] Task 3.1: list-modules Command (4h)
  - [ ] Task 3.2: show-module Command (3h)

- [ ] Final Validation (2 hours)
  - [ ] End-to-end tests
  - [ ] User acceptance test
  - [ ] Documentation review

**Total:** 25 hours (5 days)

### Milestones

- [ ] **Milestone 1:** Documentation complete (Day 2)
- [ ] **Milestone 2:** Refactoring complete (Day 4)
- [ ] **Milestone 3:** Tooling complete (Day 5)
- [ ] **Milestone 4:** All validation passed (Day 5 end)

---

## Quick Reference Card

### Files to Create (12 new)

**Documentation:**
1. `doc/guide/stdlib_quick_reference.md`
2. `doc/guide/dependency_injection_guide.md`
3. `doc/guide/mocking_guide.md`
4. `doc/guide/module_discovery_guide.md`

**Code:**
5. `src/std/__init__.spl`
6. `src/std/dependency_injection.spl`
7. `src/app/build/__init__.spl`
8. `src/app/test/__init__.spl`
9. `src/app/lint/__init__.spl`
10. `src/app/ffi_gen/__init__.spl`
11. `src/app/cli/list_modules.spl`
12. `src/app/cli/show_module.spl`

### Files to Modify (1)

1. `src/std/src/testing/__init__.spl` - Enable mocking exports

---

## Emergency Rollback Plan

If something breaks:

```bash
# Rollback Phase 3 (tooling)
jj undo  # If just committed
rm src/app/cli/list_modules.spl
rm src/app/cli/show_module.spl

# Rollback Phase 2 (refactoring)
rm src/std/__init__.spl
rm src/std/dependency_injection.spl
rm src/app/build/__init__.spl
rm src/app/test/__init__.spl
rm src/app/lint/__init__.spl
rm src/app/ffi_gen/__init__.spl
mv src/std/src/testing/__init__.spl.bak src/std/src/testing/__init__.spl

# Phase 1 (documentation) is risk-free - no rollback needed
```

---

## Next Steps

**Recommended Start:**

1. ✅ Read this checklist completely
2. ✅ Start with Task 1.1 (Stdlib Quick Reference)
3. ✅ Complete all Phase 1 tasks (Day 1-2)
4. ✅ Validate Phase 1 results
5. ✅ Decide: Continue to Phase 2, or stop at 80% benefit?

**Questions Before Starting:**
- Do you want to do Phase 1 only (80% benefit, 40% effort)?
- Do you want me to implement specific tasks?
- Do you want to review the plan first?

Let me know how you'd like to proceed!
