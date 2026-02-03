# Coverage Improvement Plan: symbol_hash.spl

**Date**: 2026-02-03
**Status**: 📋 Planned
**Module**: `lib/std/src/tooling/compiler/symbol_hash.spl`
**Current Coverage**: 0% (no tests)
**Target Coverage**: 90%+

## Executive Summary

This plan outlines comprehensive test coverage for the `symbol_hash` module, a core compiler utility responsible for symbol hashing with type tagging. The module is currently **completely untested** despite being critical for compiler symbol management.

**Why This Module?**
- ✅ Core compiler infrastructure (prevents symbol collisions)
- ✅ Zero current coverage (high ROI)
- ✅ Interpreter-compatible (pure functions, no state mutation)
- ✅ Small scope (78 lines, 10 functions)
- ✅ Deterministic behavior (easy to test)

---

## Module Analysis

### File: `lib/std/src/tooling/compiler/symbol_hash.spl`

**Size**: 78 lines of code
**Functions**: 10
**Dependencies**: None (pure utility)
**Complexity**: Moderate (polynomial hashing + bitwise operations)

### Function Inventory

| Function | Lines | Purpose | Branch Points | Test Priority |
|----------|-------|---------|---------------|---------------|
| `poly_hash(s: text)` | ~12 | Polynomial rolling hash (Horner's method) | 2 | Critical |
| `hash_symbol(symbol: text)` | ~3 | Apply type bit tag (bit 62) | 1 | Critical |
| `is_symbol_hash(hash: i64)` | ~2 | Check type tag presence | 1 | High |
| `untag_symbol_hash(hash: i64)` | ~2 | Remove type tag | 1 | High |
| `get_raw_hash(symbol: text)` | ~2 | Get untagged hash | 1 | High |
| `hash_symbols(symbols: [text])` | ~5 | Batch hash array | 2 | Medium |
| `has_collision(s1, s2: text)` | ~3 | Detect hash collision | 2 | High |
| `hash_distribution(symbols)` | ~10 | Analyze distribution | 3 | Medium |
| `all_unique_hashes(symbols)` | ~8 | Check uniqueness | 3 | Medium |
| `collision_probability(n)` | ~5 | Birthday problem calc | 2 | Low |

**Total Branch Points**: ~18

---

## Test Coverage Plan

### Test File Structure

**File**: `test/lib/std/unit/tooling/compiler/symbol_hash_spec.spl`

**Estimated Size**: 70-90 lines
**Estimated Tests**: 15-20 test cases
**Target Coverage**: 90%+ (16+ branches)

### Test Groups

#### Group 1: Core Hashing (6 tests)
**Functions**: `poly_hash`, `get_raw_hash`

| Test Case | Description | Branches Covered |
|-----------|-------------|------------------|
| T1.1 | Deterministic output for same input | poly_hash main path |
| T1.2 | Empty string returns 0 | poly_hash edge case |
| T1.3 | Single character hash | poly_hash boundary |
| T1.4 | Long string (50+ chars) | poly_hash loop |
| T1.5 | Different strings produce different hashes | poly_hash correctness |
| T1.6 | get_raw_hash matches poly_hash | get_raw_hash equivalence |

**Coverage**: 4/4 branches (100%)

#### Group 2: Symbol Tagging (6 tests)
**Functions**: `hash_symbol`, `is_symbol_hash`, `untag_symbol_hash`

| Test Case | Description | Branches Covered |
|-----------|-------------|------------------|
| T2.1 | hash_symbol sets type bit | hash_symbol path |
| T2.2 | is_symbol_hash detects tagged hash | is_symbol_hash true |
| T2.3 | is_symbol_hash rejects untagged hash | is_symbol_hash false |
| T2.4 | untag_symbol_hash round-trip | untag path |
| T2.5 | Tagging preserves hash value | bit manipulation |
| T2.6 | Multiple tagging idempotence | edge case |

**Coverage**: 4/4 branches (100%)

#### Group 3: Batch Operations (4 tests)
**Functions**: `hash_symbols`, `has_collision`

| Test Case | Description | Branches Covered |
|-----------|-------------|------------------|
| T3.1 | hash_symbols preserves length | array map |
| T3.2 | hash_symbols with empty array | edge case |
| T3.3 | has_collision: different strings | collision false |
| T3.4 | has_collision: same string | collision false (expected) |

**Coverage**: 4/4 branches (100%)

#### Group 4: Analysis Functions (4 tests)
**Functions**: `hash_distribution`, `all_unique_hashes`, `collision_probability`

| Test Case | Description | Branches Covered |
|-----------|-------------|------------------|
| T4.1 | hash_distribution counts frequencies | distribution map |
| T4.2 | all_unique_hashes: unique list | uniqueness true |
| T4.3 | all_unique_hashes: duplicates | uniqueness false |
| T4.4 | collision_probability: boundary values | math correctness |

**Coverage**: 6/6 branches (100%)

**Total Coverage**: 18/18 branches (100%)

---

## Implementation Plan

### Phase 1: Test File Setup (15 min)

1. Create directory structure:
   ```bash
   mkdir -p test/lib/std/unit/tooling/compiler
   ```

2. Create spec file with header:
   ```simple
   """
   # Symbol Hash Specification

   **Feature IDs:** #SYMBOL-HASH
   **Category:** Compiler
   **Status:** Implemented

   ## Overview

   Tests polynomial hashing with symbol type tagging for compiler use.
   Validates hash determinism, collision detection, and distribution analysis.
   """

   use std.spec.*
   use std.tooling.compiler.symbol_hash.*
   ```

### Phase 2: Core Hashing Tests (30 min)

```simple
describe "poly_hash":
    it "produces deterministic output":
        val h1 = poly_hash("hello")
        val h2 = poly_hash("hello")
        expect(h1).to(eq(h2))

    it "handles empty string":
        val h = poly_hash("")
        expect(h).to(eq(0))

    it "handles single character":
        val h = poly_hash("a")
        expect(h > 0).to(eq(true))

    it "handles long strings":
        var long = "abcdefghijklmnopqrstuvwxyz"
        long = long + long  # 52 chars
        val h = poly_hash(long)
        expect(h != 0).to(eq(true))

    it "different strings produce different hashes":
        val h1 = poly_hash("abc")
        val h2 = poly_hash("def")
        expect(h1 != h2).to(eq(true))

describe "get_raw_hash":
    it "matches poly_hash output":
        val raw = get_raw_hash("test")
        val poly = poly_hash("test")
        expect(raw).to(eq(poly))
```

### Phase 3: Symbol Tagging Tests (30 min)

```simple
describe "hash_symbol":
    it "applies type bit tag":
        val tagged = hash_symbol("my_symbol")
        val raw = poly_hash("my_symbol")
        expect(tagged != raw).to(eq(true))

    it "sets bit 62":
        val tagged = hash_symbol("test")
        expect(is_symbol_hash(tagged)).to(eq(true))

describe "is_symbol_hash":
    it "detects tagged hashes":
        val tagged = hash_symbol("foo")
        expect(is_symbol_hash(tagged)).to(eq(true))

    it "rejects untagged hashes":
        val raw = poly_hash("foo")
        expect(is_symbol_hash(raw)).to(eq(false))

describe "untag_symbol_hash":
    it "performs round-trip correctly":
        val original = poly_hash("symbol")
        val tagged = hash_symbol("symbol")
        val untagged = untag_symbol_hash(tagged)
        expect(untagged).to(eq(original))

    it "preserves hash value":
        val tagged = hash_symbol("test")
        val untagged = untag_symbol_hash(tagged)
        val expected = poly_hash("test")
        expect(untagged).to(eq(expected))
```

### Phase 4: Batch & Analysis Tests (45 min)

```simple
describe "hash_symbols":
    it "preserves array length":
        val symbols = ["a", "b", "c"]
        val hashes = hash_symbols(symbols)
        expect(hashes.len()).to(eq(3))

    it "handles empty array":
        val hashes = hash_symbols([])
        expect(hashes.len()).to(eq(0))

describe "has_collision":
    it "returns false for different strings":
        expect(has_collision("abc", "def")).to(eq(false))

    it "returns false for same string":
        # Same string = same hash, not a collision
        expect(has_collision("test", "test")).to(eq(false))

describe "hash_distribution":
    it "counts hash frequencies":
        val symbols = ["a", "b", "c", "a"]
        val dist = hash_distribution(symbols)
        expect(dist.len() <= 3).to(eq(true))

describe "all_unique_hashes":
    it "returns true for unique symbols":
        expect(all_unique_hashes(["x", "y", "z"])).to(eq(true))

    it "returns false for duplicates":
        expect(all_unique_hashes(["a", "b", "a"])).to(eq(false))

describe "collision_probability":
    it "returns 0 for n=0":
        expect(collision_probability(0)).to(eq(0.0))

    it "returns low probability for small n":
        val prob = collision_probability(10)
        expect(prob < 0.01).to(eq(true))
```

### Phase 5: Edge Cases & Validation (30 min)

```simple
describe "edge cases":
    it "handles unicode strings":
        val h = poly_hash("café")
        expect(h != 0).to(eq(true))

    it "handles special characters":
        val h = poly_hash("!@#$%^&*()")
        expect(h != 0).to(eq(true))

    it "handles very long symbol names":
        var long = "very_long_symbol_name_"
        var i = 0
        while i < 5:
            long = long + "extra_"
            i = i + 1
        val h = poly_hash(long)
        expect(h != 0).to(eq(true))

    it "tagging multiple times is idempotent":
        val h1 = hash_symbol("test")
        val h2 = hash_symbol("test")
        expect(h1).to(eq(h2))
```

---

## Verification Plan

### Build & Run Tests

```bash
# Build project
./bin/simple build

# Run symbol_hash spec
./rust/target/debug/simple_runtime \
    test/lib/std/unit/tooling/compiler/symbol_hash_spec.spl

# Expected output:
# poly_hash: 5 examples, 0 failures
# get_raw_hash: 1 example, 0 failures
# hash_symbol: 2 examples, 0 failures
# is_symbol_hash: 2 examples, 0 failures
# untag_symbol_hash: 2 examples, 0 failures
# hash_symbols: 2 examples, 0 failures
# has_collision: 2 examples, 0 failures
# hash_distribution: 1 example, 0 failures
# all_unique_hashes: 2 examples, 0 failures
# collision_probability: 2 examples, 0 failures
# edge cases: 4 examples, 0 failures
# Total: 25 examples, 0 failures
```

### Coverage Validation

```bash
# Run via cargo test
cargo test --package simple-driver \
    --test simple_stdlib_tests \
    symbol_hash_spec

# Verify all functions are called
# Expected: 10/10 functions covered (100%)
```

---

## Success Metrics

| Metric | Target | Validation |
|--------|--------|------------|
| **Function Coverage** | 10/10 (100%) | All functions have ≥1 test |
| **Branch Coverage** | 16/18 (90%+) | All main paths + edge cases |
| **Test Count** | 20-25 tests | Comprehensive coverage |
| **Execution Time** | <100ms | Fast feedback loop |
| **Test Failures** | 0 | All tests pass |

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Hash algorithm change | Low | High | Document expected outputs |
| Interpreter limitations | Low | Low | Pure functions, no state |
| Type system issues | Medium | Low | Use explicit type annotations |
| Missing edge cases | Medium | Medium | Peer review test cases |

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| Phase 1: Setup | 15 min | Test file skeleton |
| Phase 2: Core Hashing | 30 min | 6 tests (poly_hash, get_raw_hash) |
| Phase 3: Tagging | 30 min | 6 tests (hash_symbol, is/untag) |
| Phase 4: Batch/Analysis | 45 min | 8 tests (hash_symbols, collision, etc.) |
| Phase 5: Edge Cases | 30 min | 4-5 tests (unicode, long strings) |
| **Total** | **2.5 hours** | **25 tests, 90%+ coverage** |

---

## Follow-Up Recommendations

After completing `symbol_hash.spl`:

1. **string_escape.spl** (123 lines) - Lexer escape sequences
2. **severity.spl** (90 lines) - Diagnostic severity levels
3. **layout.spl** (163 lines) - FFI struct layout calculations

These modules share similar characteristics: pure functions, no state, critical to compiler, currently untested.

---

## Appendix: Module Source Reference

**File**: `/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/compiler/symbol_hash.spl`

**Key Algorithm**: Polynomial rolling hash using Horner's method
**Type Tagging**: Bit 62 distinguishes symbol hashes from other hash types
**Use Case**: Compiler symbol table, prevents naming collisions, type-safe hashing

**Dependencies**: None (pure utility)
**Exports**: All 10 functions (public API)
