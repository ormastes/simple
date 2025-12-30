# BDD Feature Spec Progress

**Last Updated:** 2025-12-30
**Goal:** Replace all old feature documentation with BDD-generated documentation

## Progress Summary

| Status | Count | Percentage |
|--------|-------|------------|
| ✅ Complete | 21 | 42% |
| 📋 Planned | 29 | 58% |
| **Total** | **50** | - |

**Current:** 21 specs, 180 tests passing

---

## Completed BDD Specs (21)

### Infrastructure (2/9)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #1 | Lexer | 9 | ✅ |
| #2 | Parser | 9 | ✅ |
| #3 | AST | - | 📋 |
| #4 | HIR | - | 📋 |
| #5 | MIR | - | 📋 |
| #6 | RuntimeValue | - | 📋 |
| #7 | GC | - | 📋 |
| #8 | Package Manager | - | 📋 |
| #9 | SMF | - | 📋 |

### Types (4/6)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #10 | Basic Types | 9 | ✅ |
| #16 | Enums | 7 | ✅ |
| #27 | Option/Result | 9 | ✅ |
| #30 | Operators | 15 | ✅ |
| #18 | Memory Types | - | 📋 |
| #19 | Borrowing | - | 📋 |

### Language (7/10)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #11 | Classes | 5 | ✅ |
| #12 | Functions | 8 | ✅ |
| #14 | Structs | 7 | ✅ |
| #15 | Variables | 10 | ✅ |
| #17 | Methods | 8 | ✅ |
| #24 | Closures | 9 | ✅ |
| #28 | Imports | 8 | ✅ |
| #29 | Macros | - | 📋 |
| #31 | Traits | - | 📋 |
| #32 | Generics | - | 📋 |

### Data Structures (4/6)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #20 | Arrays | 11 | ✅ |
| #21 | Dicts | 9 | ✅ |
| #25 | Strings | 10 | ✅ |
| #26 | Tuples | 9 | ✅ |
| #33 | Sets | - | 📋 |
| #34 | Ranges | - | 📋 |

### Control Flow (3/4)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #13 | Loops | 7 | ✅ |
| #90 | Match Expressions | 7 | ✅ |
| #91 | Conditionals | 10 | ✅ |
| #35 | Error Handling | - | 📋 |

### Concurrency (0/4)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #40 | Actors | - | 📋 |
| #41 | Async/Await | - | 📋 |
| #42 | Generators | - | 📋 |
| #43 | Futures | - | 📋 |

### Codegen (1/4)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #100 | Cranelift Backend | 4 | ✅ |
| #95 | Capture Buffer | - | 📋 |
| #96 | Generator Codegen | - | 📋 |
| #97 | LLVM Backend | - | 📋 |

### Testing Framework (0/7)

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #180 | describe blocks | - | 📋 |
| #181 | context blocks | - | 📋 |
| #182 | it examples | - | 📋 |
| #183 | before_each | - | 📋 |
| #184 | after_each | - | 📋 |
| #187 | expect matchers | - | 📋 |
| #192 | Doctest | - | 📋 |

---

## Priority Queue

### High Priority (Core Language)
1. **#29 Macros** - Metaprogramming essential
2. **#31 Traits** - Interface definitions
3. **#32 Generics** - Type parameterization
4. **#35 Error Handling** - try/catch/raise

### Medium Priority (Infrastructure)
5. **#3 AST** - Abstract syntax tree
6. **#4 HIR** - High-level IR
7. **#5 MIR** - Mid-level IR
8. **#9 SMF** - Binary format

### Medium Priority (Concurrency)
9. **#41 Async/Await** - Asynchronous programming
10. **#42 Generators** - yield-based iteration
11. **#40 Actors** - Message passing
12. **#43 Futures** - Promise-based async

### Lower Priority (Advanced)
13. **#18 Memory Types** - Reference capabilities
14. **#19 Borrowing** - Ownership semantics
15. **#33 Sets** - Set data structure
16. **#34 Ranges** - Range expressions

### Testing Framework (Self-referential)
17. **#180-#187** - BDD framework specs
18. **#192** - Doctest specs

---

## Session History

| Date | Specs Added | Tests Added | Total Specs | Total Tests |
|------|-------------|-------------|-------------|-------------|
| 2025-12-29 | 8 | 62 | 8 | 62 |
| 2025-12-30 (AM) | 7 | 59 | 15 | 121 |
| 2025-12-30 (PM) | 6 | 59 | 21 | 180 |

---

## How to Add New Specs

1. Create spec file: `simple/std_lib/test/features/{category}/{feature}_spec.spl`
2. Use FeatureMetadata class for metadata
3. Write BDD-style tests with pass/fail tracking
4. Create doc file: `doc/features/{category}/{id}_{feature}.md`
5. Update category `__index__.md`
6. Update this progress document
7. Update `feature.md` stats

### Spec Template

```simple
# Feature Specification
# Feature #XX: Name
# Category: Category | Difficulty: N | Status: Complete

class FeatureMetadata:
    id: Int
    name: String
    category: String
    # ... (see existing specs for full template)

let FEATURE = FeatureMetadata { ... }

let mut passed = 0
let mut failed = 0

print('describe Feature:')
print('  it does something:')
if condition:
    print('    [PASS] description')
    passed = passed + 1
else:
    print('    [FAIL] description')
    failed = failed + 1

# ... more tests

print('Passed: {passed}')
print('Failed: {failed}')
if failed == 0:
    print('All tests PASSED!')
```

---

## Related Files

- [feature.md](feature.md) - Main feature overview
- [__index__.md](__index__.md) - Feature index
- `simple/std_lib/test/features/` - BDD spec tests
- `doc/features/{category}/` - Generated documentation
