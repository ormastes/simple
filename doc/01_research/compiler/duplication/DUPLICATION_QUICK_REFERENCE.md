# Stdlib Duplication Quick Reference

**Last Updated:** 2026-02-14
**Scope:** src/lib/ core utility modules
**Duplications Found:** 10 semantic duplications

---

## Critical Duplications (Immediate Action)

### 1. binary_search()
| Module | Lines | Type | Status |
|--------|-------|------|--------|
| `algorithm_utils.spl` | ~35 | i64 array, typed | **CANONICAL** |
| `search_utils.spl` | ~35 | untyped array | Duplicate |

**Action:** Remove from search_utils, re-export from algorithm_utils

---

### 2. linear_search()
| Module | Lines | Type | Status |
|--------|-------|------|--------|
| `algorithm_utils.spl` | 12 | i64 array, typed | **CANONICAL** |
| `search_utils.spl` | 12 | untyped array | Duplicate |

**Action:** Remove from search_utils, re-export from algorithm_utils

---

### 3. find_min() / find_max()
| Module | Lines | Type | Status |
|--------|-------|------|--------|
| `algorithm_utils.spl` | ~12 each | i64 array, typed | **CANONICAL** |
| `search_utils.spl` | ~12 each | untyped array | Duplicate |

**Action:** Remove from search_utils, re-export from algorithm_utils

---

### 4. is_sorted()
| Module | Lines | Type | Status |
|--------|-------|------|--------|
| `algorithm_utils.spl` | 8 | i64 array, for loop | **CANONICAL** |
| `comparator_utils.spl` | 8 | untyped array, while loop | Duplicate |
| `list_utils.spl` | 8 | i64 array, for loop | Duplicate |

**Action:** Keep algorithm_utils as canonical. Remove from comparator_utils and list_utils (re-export).

---

## Maintenance Burden Duplications

### 5. take()
| Module | Lines | Status |
|--------|-------|--------|
| `algorithm_utils.spl` | 5 | **CANONICAL** |
| `functional.spl` | 5 | Duplicate |
| `list_utils.spl` | 5 | Duplicate |

---

### 6. drop()
| Module | Lines | Status |
|--------|-------|--------|
| `algorithm_utils.spl` | 5 | **CANONICAL** |
| `list_utils.spl` | 5 | Duplicate |

---

### 7. count_occurrences()
| Module | Lines | Status |
|--------|-------|--------|
| `algorithm_utils.spl` | 9 | **CANONICAL** |
| `search_utils.spl` | 9 | Duplicate |

---

### 8. reverse_list()
| Module | Lines | Status |
|--------|-------|--------|
| `algorithm_utils.spl` | 10 | **CANONICAL** |
| `list_utils.spl` | 10 | Duplicate |

---

### 9. remove_duplicates()
| Module | Lines | Status |
|--------|-------|--------|
| `algorithm_utils.spl` | 8 | **CANONICAL** |
| `collection_utils.spl` | 8 | Duplicate |

---

### 10. median()
| Module | Lines | Approach | Status |
|--------|-------|----------|--------|
| `collection_utils.spl` | 12 | Assumes sorted, simple indexing | Variant A |
| `comparator_utils.spl` | 10 | Integer division | Variant B |
| `math.spl` | 17 | Includes sorting, bubble sort | Variant C |
| `stats_utils.spl` | 14 | Averaging for even-length | Variant D |

**Action:** Clarify API contract, consolidate into single `math_utils.spl` with clear semantics

---

## Module Responsibility Matrix

| Function | Canonical Location | Also In | Action |
|----------|-------------------|---------|--------|
| binary_search | algorithm_utils | search_utils | Remove from search_utils |
| linear_search | algorithm_utils | search_utils | Remove from search_utils |
| find_min | algorithm_utils | search_utils | Remove from search_utils |
| find_max | algorithm_utils | search_utils | Remove from search_utils |
| count_occurrences | algorithm_utils | search_utils | Remove from search_utils |
| is_sorted | algorithm_utils | comparator_utils, list_utils | Remove from others |
| reverse_list | algorithm_utils | list_utils | Remove from list_utils |
| take | algorithm_utils | functional, list_utils | Remove from others |
| drop | algorithm_utils | list_utils | Remove from list_utils |
| remove_duplicates | algorithm_utils | collection_utils | Remove from collection_utils |
| median | (TBD) | collection_utils, comparator_utils, math, stats | Consolidate strategy |

---

## False Positives (Do NOT consolidate)

### rotate_left() / rotate_right()
**Why:** Different types (bit rotation vs list rotation vs tuple rotation)
- `bitwise_utils.spl` - operates on i64 (bit level)
- `list_utils.spl` - operates on [i64] (list level)
- `tuple_utils.spl` - operates on tuples (element level)

These are **correct polymorphic instances**, not duplications.

---

## Consolidation Estimate

### Phase 1: Core Algorithms (Low Risk)
**Functions to consolidate:** binary_search, linear_search, find_min, find_max, count_occurrences, is_sorted, reverse_list, take, drop, remove_duplicates

**Effort:** 4-6 hours
- Move canonical versions to algorithm_utils.spl (if not already)
- Add re-exports to affected modules
- Update tests to use canonical locations

**Risk:** LOW (backward compatible via re-exports)

---

### Phase 2: Typed Variants (Medium Risk)
**Functions:** Same as Phase 1, but create type-specific wrappers

**Effort:** 2-3 hours
- For each duplicated function, create thin wrapper in specialized module
- Document type choice rationale

**Risk:** MEDIUM (type conversion edge cases)

---

### Phase 3: Semantic Variants (High Risk)
**Functions:** median() family

**Effort:** 3-4 hours
- Decide on canonical semantics (averaging vs integer division)
- Create separate functions for different behaviors if needed
- Update all test suites

**Risk:** HIGH (API breaking change potential)

---

## Prevention Measures

### For Code Review
Add checklist item:
- [ ] Check for duplicate function signatures across other modules
- [ ] Verify function not already defined in canonical location

### For Linting
Add rule to detect:
- Same function name in 2+ modules
- Same function signature with different implementations
- Suggest moving to canonical module

### For Documentation
Update CLAUDE.md:
```
## Stdlib Module Responsibilities

- algorithm_utils.spl:   Core sorting, searching, list algorithms (CANONICAL)
- search_utils.spl:      Specialized search variants (exponential, interpolation, etc.)
- list_utils.spl:        List-specific operations (chunk, flatten, interleave, etc.)
- collection_utils.spl:  Collection algorithms (transpose, powerset, etc.)
- comparator_utils.spl:  Comparison and sorting strategies
- functional.spl:        Functional programming operations
- statistics_utils.spl:  Statistical calculations

DO NOT duplicate functions already in algorithm_utils!
```

---

## Related Documentation

- **Full Analysis:** `doc/analysis/phase2_std_duplicates.md` (583 lines)
- **Phase 1 Analysis:** `doc/analysis/phase1_duplicates.md`
- **Implementation Plan:** (to be created)

---

**Status:** Quick reference complete
**Next Step:** Phase 1 consolidation PR
