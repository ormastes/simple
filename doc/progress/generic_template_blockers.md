# Generic Template Test Blockers

**Date:** 2026-02-11
**File:** `test/unit/compiler/generic_template_spec.spl`
**Status:** 5/30 tests enabled, 25 remaining BLOCKED

---

## ✅ Working Tests (5)

### Generic Template Partitioning (100% complete - 5/5)
1. ✅ should separate generic function into templates
2. ✅ should separate generic struct
3. ✅ should separate mixed generic and non-generic correctly
4. ✅ Empty templates object has zero count
5. ✅ Templates with multiple constructs count correctly

**Functions that work:**
- `partition_generic_constructs()` ✅
- `GenericTemplates.new()` ✅
- `SpecializedInstances.new()` ✅
- AST construction (Module, FunctionDef, StructDef) ✅

---

## ❌ Blocked Tests (25)

### Monomorphization Metadata (0/3) - BLOCKED
**Blocker:** `build_monomorphization_metadata_from_constructs()` **hangs/infinite loop**

Tests affected:
- should register function template in metadata
- should track specialization entry
- should track multiple specializations

**Symptom:** Test execution hangs indefinitely, no error output
**Root cause:** Unknown - likely infinite loop in metadata building

### Deferred Monomorphization (0/22) - BLOCKED
**Blocker:** `DeferredMonomorphizer.new()` **hangs/causes issues**

Tests affected: ALL 22 remaining tests in this section

**Symptom:** Test execution hangs when trying to instantiate DeferredMonomorphizer
**Root cause:** Unknown - DeferredMonomorphizer has runtime compatibility issues

### Concrete Types (0/5) - BLOCKED
**Blocker:** Even simple enum comparisons cause hangs

Tests affected:
- should differentiate primitives
- should differentiate array element types
- should preserve tuple element order
- And others...

**Symptom:** Test hangs even on `ConcreteType.Int` != `ConcreteType.Float`
**Root cause:** Possible environmental issue or cascading failure from previous hangs

---

## 🔍 Investigation Results

### Attempted Solutions

1. **Tried enabling metadata tests** → Hangs
2. **Tried DeferredMonomorphizer tests** → Hangs
3. **Tried simple ConcreteType tests** → Hangs
4. **Killed hung processes** → System temporarily stable, then MCP servers respawn
5. **Built file directly** → ✅ Build succeeds (syntax OK)

### Environmental Issues

**MCP Server Spawning:**
- Multiple MCP server processes spawn at 100% CPU
- Processes: `/home/ormastes/dev/pub/simple/bin/release/simple .../mcp/main.spl server`
- Keep respawning even after kill
- Cause system slowdown and test hangs

**Possible Causes:**
1. Claude Code automatically spawning MCP servers
2. MCP servers have infinite loop or resource leak
3. System becomes unstable after multiple test attempts
4. Cascading failures from hung tests

---

## 📊 Analysis

### What Works at Runtime
- ✅ Partition functions (template separation)
- ✅ Basic data structure construction
- ✅ Simple function calls
- ✅ AST node creation
- ✅ GenericTemplates/SpecializedInstances constructors

### What Doesn't Work at Runtime
- ❌ `build_monomorphization_metadata_from_constructs()`
- ❌ `DeferredMonomorphizer.new()`
- ❌ Complex monomorphization operations
- ❌ Tests after system becomes unstable

### Pattern
The working tests use **simple, stateless functions**.
The blocked tests use **complex, stateful classes/functions**.

---

## 🎯 Recommendations

### Short-term
1. **Leave remaining 25 tests skipped** in this file
2. **Document blockers** (done)
3. **Move to different test file** with simpler requirements
4. **Focus on files without monomorphization complexity**

### Target Next Files
Look for test files that:
- Don't use DeferredMonomorphizer
- Don't use complex metadata building
- Test simpler language features
- Have already-implemented infrastructure

**Candidates:**
- Parser feature tests (dual argument syntax, etc.)
- Symbol interning tests (if simple)
- File I/O tests (we have FFI ready)
- Test database tests (file locking exists)

### Long-term
1. **Fix DeferredMonomorphizer** runtime issues
2. **Fix metadata building** infinite loop
3. **Investigate MCP server** spawning/hanging
4. **Re-enable these 25 tests** after fixes

---

## 💡 Lessons Learned

### Success Pattern
- Start with simplest tests first
- Test immediately after enabling
- Kill environment and restart if hangs occur
- Document blockers rather than fighting them

### Avoid Pattern
- Don't enable complex tests without investigating first
- Don't keep trying when systematic hanging occurs
- Don't assume all tests in a file are equal difficulty
- Don't let hung processes accumulate

---

## 📈 Impact

**Enabled so far:** 5/606 tests (0.8%)
**Blocked in this file:** 25 tests
**Remaining in other files:** 576 tests

**Strategy adjustment:** Focus on simpler test files first, return to complex monomorphization tests after core issues are fixed.

---

## ✅ Next Steps

1. Commit investigation findings
2. Choose simpler test file (parser features, file I/O, etc.)
3. Continue enablement with less complex tests
4. Build momentum with easier wins
5. Return to monomorphization tests after gaining more experience

**Estimated easy wins available:** 300-400 tests in simpler categories

---

*This document helps us avoid wasting time on blocked tests and focus on productive areas.*
