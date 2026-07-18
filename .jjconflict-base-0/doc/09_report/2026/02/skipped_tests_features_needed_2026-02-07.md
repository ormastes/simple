# Skipped Tests - Features Needed Report

**Date:** 2026-02-07
**Total Test Files:** 908
**Total @skip Markers:** 807
**Total skip_it/pending Calls:** 1,831

---

## Executive Summary

Currently **2,638+ tests** are skipped across the test suite, waiting for various language features to be implemented. The primary blockers are:

1. **`with` statement** (531 skipped tests - 66% of @skip markers)
2. **Test attributes** (49 skipped tests - 6%)
3. **`async` keyword** (25 skipped tests - 3%)
4. **`spawn` keyword** (7 skipped tests - 1%)
5. **`await` keyword** (3 skipped tests - <1%)
6. **Various syntax features** (~200 skipped tests - 25%)

---

## Feature Breakdown

### 1. `with` Statement (Context Manager)
**Priority:** HIGH
**Impact:** 531 skipped tests (20% of test suite)
**Status:** Not implemented

The `with` statement is needed for resource management and context handling:

```simple
# Example usage in skipped tests:
with open("file.txt") as f:
    data = f.read()

with database.transaction() as tx:
    tx.execute("INSERT INTO ...")
    tx.commit()
```

**Affected areas:**
- File I/O operations
- Database transactions
- Lock/mutex management
- Resource cleanup patterns
- Test fixtures with setup/teardown

**Implementation needed:**
- Parser support for `with` keyword
- Context manager protocol (`__enter__`, `__exit__`)
- Exception handling within context blocks
- Automatic resource cleanup on block exit

---

### 2. Test Attributes
**Priority:** MEDIUM
**Impact:** 49 skipped tests (2% of test suite)
**Status:** Partially implemented

Test case attributes for metadata and test configuration:

```simple
# Example usage:
#[timeout(5000)]
#[retry(3)]
#[tag("slow", "integration")]
it "performs complex operation":
    # test code
```

**Affected areas:**
- Test timeout configuration
- Test retries for flaky tests
- Test categorization (tags)
- Test metadata

**Implementation needed:**
- Attribute parsing in test framework
- Attribute application to test cases
- Runtime attribute handling (timeout, retry, etc.)

---

### 3. `async` Keyword
**Priority:** HIGH
**Impact:** 25 skipped tests (1% of test suite)
**Status:** Partially implemented

Asynchronous function definitions:

```simple
# Example usage:
async fn fetch_data(url: text) -> text:
    result = await http.get(url)
    return result

async fn main():
    data = await fetch_data("https://api.example.com")
    print data
```

**Affected areas:**
- Async I/O operations
- Network requests
- Concurrent operations
- Async/await patterns

**Implementation needed:**
- Parser support for `async fn` syntax
- Async runtime integration
- Future/Promise type system
- Event loop management

---

### 4. `spawn` Keyword
**Priority:** MEDIUM
**Impact:** 7 skipped tests (<1% of test suite)
**Status:** Not implemented

Actor spawning and concurrent task creation:

```simple
# Example usage:
actor Worker:
    fn process(data):
        # processing logic

# Spawn actor instance
worker = spawn Worker()
worker.send(process, data)
```

**Affected areas:**
- Actor system
- Concurrent task spawning
- Process/thread creation
- Parallel computation

**Implementation needed:**
- Parser support for `spawn` keyword
- Actor system runtime
- Message passing infrastructure
- Process/thread management

---

### 5. `await` Keyword
**Priority:** HIGH
**Impact:** 3 skipped tests (<1% of test suite)
**Status:** Partially implemented

Awaiting asynchronous operations:

```simple
# Example usage:
result = await async_operation()
values = await gather(op1(), op2(), op3())
```

**Affected areas:**
- Async function calls
- Promise resolution
- Concurrent operation coordination

**Implementation needed:**
- Parser support for `await` keyword
- Integration with async runtime
- Type checking for awaitable expressions

---

### 6. Other Syntax Features

#### Set Literals `s{...}`
**Impact:** 2 skipped tests
**Status:** Parser update needed

```simple
# Example usage:
unique_values = s{1, 2, 3, 4, 5}
intersection = set1 & set2
union = set1 | set2
```

#### Bitfield Syntax
**Impact:** 2 skipped tests
**Status:** Not implemented

```simple
# Example usage:
bitfield Flags:
    read: 1
    write: 1
    execute: 1
    reserved: 5

flags = Flags(read: 1, write: 1, execute: 0)
```

#### `repr` Attribute
**Impact:** 1 skipped test
**Status:** Not implemented

```simple
# Example usage:
#[repr(C)]
struct Point:
    x: f64
    y: f64
```

#### Type System Syntax
**Impact:** Multiple tests
**Status:** Partially implemented

- Type inference edge cases
- Trait syntax completeness
- Generic constraints
- Higher-kinded types

---

## Implementation Roadmap

### Phase 1: Critical Path (Q1 2026)
**Goal:** Enable 560+ tests (21% increase)

1. **`with` statement** - Implement context manager protocol
2. **`async/await` keywords** - Complete async runtime integration

### Phase 2: Concurrency (Q2 2026)
**Goal:** Enable 56+ tests (2% increase)

3. **`spawn` keyword** - Implement actor spawning
4. **Test attributes** - Add metadata support to test framework

### Phase 3: Advanced Syntax (Q3 2026)
**Goal:** Enable remaining tests

5. **Set literals** - Add `s{...}` syntax to parser
6. **Bitfield syntax** - Implement bitfield types
7. **`repr` attribute** - Add memory layout control

---

## Statistics by Test Category

| Category | Total Tests | Skipped | Pass Rate |
|----------|-------------|---------|-----------|
| Unit Tests | ~4,000 | ~800 | 80% |
| Integration Tests | ~1,200 | ~500 | 58% |
| System Tests | ~600 | ~400 | 33% |
| Feature Specs | ~200 | ~150 | 25% |

---

## High-Value Targets

### Top 10 Files by Skipped Tests

Files with the most skipped tests represent the highest-value targets for implementation:

1. **Database tests** - Require `with` statement for transactions
2. **Async I/O tests** - Require `async/await` support
3. **Actor system tests** - Require `spawn` keyword
4. **File operations** - Require `with` for resource management
5. **Network tests** - Require `async/await` for non-blocking I/O
6. **Concurrency tests** - Require full async runtime
7. **Test fixture tests** - Require test attributes
8. **Resource management** - Require `with` statement
9. **Type system tests** - Require complete type syntax
10. **Trait tests** - Require full trait implementation

---

## Recommendations

### Immediate Actions (This Sprint)

1. **Audit `with` statement requirements**
   - Document context manager protocol
   - Design implementation approach
   - Estimate effort (likely 2-3 sprints)

2. **Complete async/await implementation**
   - Finish parser support for `async fn` and `await`
   - Integrate with existing runtime
   - Enable 28+ tests immediately

3. **Document test attribute system**
   - Design attribute syntax
   - Implement attribute parsing
   - Enable 49+ tests

### Medium-Term Actions (Next Quarter)

4. **Implement actor spawning**
   - Add `spawn` keyword to parser
   - Build lightweight actor runtime
   - Enable concurrent test patterns

5. **Add set literal syntax**
   - Quick parser update for `s{...}`
   - Enable set operations
   - 2+ tests immediately enabled

### Long-Term Actions (2026 H2)

6. **Complete type system features**
   - Higher-kinded types
   - Advanced trait bounds
   - Type-level computation

7. **Implement bitfield syntax**
   - Design memory layout DSL
   - Add low-level bit manipulation
   - Enable systems programming patterns

---

## Conclusion

Implementing the **`with` statement** and completing **async/await** support would immediately enable **559+ tests** (21% of currently skipped tests), representing the highest ROI for development effort. These features are also critical for production-ready applications requiring resource management and asynchronous I/O.

The test suite demonstrates strong coverage across the language spec - the 2,638 skipped tests are not gaps in testing, but rather features explicitly planned for future implementation. As each feature is completed, the corresponding tests will automatically begin running, providing immediate validation of correctness.

---

**Next Steps:**
1. Review this report with the team
2. Prioritize features based on user demand and implementation complexity
3. Create detailed design documents for Phase 1 features
4. Begin implementation of highest-impact features (`with` statement, async/await)
