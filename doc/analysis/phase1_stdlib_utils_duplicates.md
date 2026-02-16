# Standard Library Utils Duplication Analysis - Phase 1

**Analysis Date:** 2026-02-14
**Scope:** All `*_utils.spl` files in `src/std/`
**Method:** Token-based similarity analysis with 5-line sliding windows

---

## Executive Summary

**Files Analyzed:** 31 utility files
**Total Lines:** 15,284 lines of code
**Duplicate Blocks Found:** 1,151 instances (5-line windows with 3+ significant lines)
**Total Duplicate Occurrences:** 2,461
**Duplication Rate:** ~16% of code appears in duplicate patterns

**Impact:** HIGH - Significant consolidation opportunity

---

## Files Analyzed

1. `src/std/algorithm_utils.spl`
2. `src/std/amqp_utils.spl`
3. `src/std/bitwise_utils.spl`
4. `src/std/collection_utils.spl`
5. `src/std/combinatorics_utils.spl`
6. `src/std/comparator_utils.spl`
7. `src/std/ds_utils.spl`
8. `src/std/encoding_utils.spl`
9. `src/std/format_utils.spl`
10. `src/std/ftp_utils.spl`
11. `src/std/gzip_utils.spl`
12. `src/std/hash_utils.spl`
13. `src/std/html_parser_utils.spl`
14. `src/std/json_parser_utils.spl`
15. `src/std/list_utils.spl`
16. `src/std/matrix_utils.spl`
17. `src/std/predicate_utils.spl`
18. `src/std/probability_utils.spl`
19. `src/std/random_utils.spl`
20. `src/std/range_utils.spl`
21. `src/std/regex_engine/char_utils.spl`
22. `src/std/search_utils.spl`
23. `src/std/set_utils.spl`
24. `src/std/skiplist_utils.spl`
25. `src/std/src/text_utils.spl`
26. `src/std/src/tooling/regex_utils.spl`
27. `src/std/stats_utils.spl`
28. `src/std/text_utils.spl`
29. `src/std/tuple_utils.spl`
30. `src/std/udp_utils.spl`
31. `src/std/validation_utils.spl`

---

## Pattern Analysis

### 1. Iteration Boilerplate (HIGH PRIORITY)

**Occurrences:** 179 `while i <` loops, 496 `.len()` calls

**Pattern:**
```simple
var result = []
var i = 0
while i < arr.len():
    # process arr[i]
    result = result + [item]
    i = i + 1
```

**Impact:** 30+ lines of savings per consolidation

**Recommendation:** Create `std.iteration` module with:
- `fn each(arr, fn)` - Iterate with callback
- `fn map(arr, fn)` - Transform elements
- `fn filter(arr, predicate)` - Filter elements
- `fn reduce(arr, init, fn)` - Accumulate results

---

### 2. String Processing Loops (7 occurrences)

**Location:** `encoding_utils.spl` (lines 293, 351, 380, and 4 more)

**Pattern:**
```simple
var result = ""
var i = 0
while i < s.len():
    val c = s[i]
    # character processing
    result = result + transformed_char
    i = i + 1
```

**Impact:** 25+ lines

**Recommendation:** Create `fn string_transform(s: text, transform_fn: fn(ch: text) -> text) -> text`

---

### 3. Array Comparison Logic (6 occurrences)

**Location:** `collection_utils.spl` (lines 387, 404, 422, and 3 more)

**Pattern:**
```simple
while i < arr1.len():
    if arr1[i] != arr2[i]:
        return false
    i = i + 1
true
```

**Impact:** 18 lines

**Recommendation:** Create `fn arrays_equal(arr1, arr2) -> bool` helper

---

### 4. Matrix Building Patterns (6 occurrences)

**Location:** `matrix_utils.spl` (lines 294, 321, 372, and 3 more)

**Pattern:**
```simple
var result = []
var i = 0
while i < rows:
    var row = []
    var j = 0
    while j < cols:
        row.push(compute_element(i, j))
        j = j + 1
    result.push(row)
    i = i + 1
result
```

**Impact:** 40+ lines

**Recommendation:** Create `fn matrix_build(rows, cols, element_fn) -> matrix` helper

---

### 5. Binary Search Pattern (5 occurrences)

**Location:** `search_utils.spl` (lines 111, 133, 156, and 2 more)

**Pattern:**
```simple
while left <= right:
    val mid = left + (right - left) / 2
    if arr[mid] == target:
        return mid
    elif arr[mid] < target:
        left = mid + 1
    else:
        right = mid - 1
-1
```

**Impact:** 30 lines

**Recommendation:** Create generic `fn binary_search(arr, target, compare_fn) -> i64` in `search_utils.spl`

---

### 6. Struct Copy Pattern (5 occurrences)

**Location:** `udp_utils.spl` (lines 361, 375, 393, and 2 more)

**Pattern:**
```simple
val new_socket = UdpSocket(
    address: socket.address,
    port: socket.port,
    state: socket.state,
    field_to_modify: new_value,
    # ... 10+ fields copied verbatim
)
```

**Impact:** 50+ lines

**Recommendation:** Implement struct update syntax or helper: `fn socket_with_field(socket, field, value)`

---

### 7. Validation Helper Duplication (LOW PRIORITY)

**Functions starting with `is_`:** 88 functions
**Functions starting with `get_`:** 43 functions
**Functions starting with `to_`:** 6 functions

**Impact:** Mostly protocol-specific, consolidation not recommended

---

## Common Helper Patterns

### Predicate Functions (88 occurrences)

Most `is_*` functions follow a pattern:
```simple
fn is_condition(x: type) -> bool:
    x <comparison> value
```

**Consolidation Opportunity:** Template-based generation or macro system

### Accessor Functions (43 occurrences)

Tuple accessors like `get_1`, `get_2`, etc. are repetitive:
```simple
fn get_N(tuple):
    tuple.N
```

**Recommendation:** Built-in tuple indexing syntax

---

## Consolidation Recommendations

### High Priority (30-50 lines savings each)

1. **Iteration Module** (`src/std/iteration.spl`)
   - `each`, `map`, `filter`, `reduce`, `fold`
   - **Savings:** ~200 lines across all utils
   - **Complexity:** Low

2. **String Transform Helpers** (add to `src/std/text.spl`)
   - `string_map(s, fn)` - Character-by-character transformation
   - `string_filter(s, predicate)` - Filter characters
   - **Savings:** ~100 lines
   - **Complexity:** Low

3. **Matrix Builder** (add to `matrix_utils.spl`)
   - `matrix_build(rows, cols, fn)`
   - `matrix_from_fn(rows, cols, fn)`
   - **Savings:** ~150 lines
   - **Complexity:** Medium

4. **Generic Binary Search** (consolidate in `search_utils.spl`)
   - `binary_search_with(arr, target, compare_fn)`
   - **Savings:** ~120 lines
   - **Complexity:** Low

### Medium Priority (10-20 lines savings each)

5. **Array Comparison** (add to `collection_utils.spl`)
   - `arrays_equal(arr1, arr2)`
   - `arrays_equal_with(arr1, arr2, compare_fn)`
   - **Savings:** ~60 lines
   - **Complexity:** Low

6. **Struct Copy Helpers** (add to specific utils)
   - `socket_with_*` helper functions
   - **Savings:** ~80 lines (UDP utils only)
   - **Complexity:** Medium (requires code generation or macros)

### Low Priority (Language Feature Needed)

7. **Tuple Accessors** - Wait for built-in syntax
8. **Predicate Generation** - Wait for macro system or code generation

---

## Metrics Summary

| Category | Count | Lines | Consolidation Potential |
|----------|-------|-------|------------------------|
| Iteration loops | 179 | ~1,200 | HIGH (iteration module) |
| String transforms | 7 | ~100 | HIGH (string helpers) |
| Matrix builders | 6 | ~150 | HIGH (matrix_build fn) |
| Binary search | 5 | ~120 | HIGH (generic search) |
| Array comparisons | 6 | ~60 | MEDIUM (helper fn) |
| Struct copies | 5 | ~80 | MEDIUM (requires lang feature) |
| Predicate funcs | 88 | ~350 | LOW (mostly protocol-specific) |
| Accessor funcs | 43 | ~200 | LOW (needs lang syntax) |

**Total Consolidation Potential:** ~800-1,000 lines (5-7% reduction)

---

## Next Steps

1. **Create Iteration Module** (`src/std/iteration.spl`)
   - Priority: HIGH
   - Effort: 2-3 hours
   - Impact: 200+ lines saved

2. **Add String Transform Helpers** to `src/std/text.spl`
   - Priority: HIGH
   - Effort: 1-2 hours
   - Impact: 100+ lines saved

3. **Consolidate Binary Search** in `src/std/search_utils.spl`
   - Priority: HIGH
   - Effort: 1 hour
   - Impact: 120+ lines saved

4. **Add Matrix Builder** to `src/std/matrix_utils.spl`
   - Priority: MEDIUM
   - Effort: 2 hours
   - Impact: 150+ lines saved

5. **Add Array Comparison** to `src/std/collection_utils.spl`
   - Priority: MEDIUM
   - Effort: 30 minutes
   - Impact: 60+ lines saved

6. **Review Struct Copy Patterns** - Consider language feature for struct update syntax
   - Priority: LOW (requires design discussion)
   - Effort: N/A
   - Impact: 80+ lines (long-term)

---

## Files Generated

- `doc/analysis/stdlib_utils_files.txt` - List of 31 analyzed files
- `doc/analysis/stdlib_utils_concatenated.spl` - Full concatenated source (15,284 lines)
- `doc/analysis/pattern_analysis.txt` - Detailed pattern breakdown
- `doc/analysis/phase1_stdlib_utils_duplicates.md` - This report

---

## Technical Notes

- Analysis performed using 5-line sliding window with MD5 hashing
- Minimum 3 significant lines (non-empty, non-comment) per block
- Normalized whitespace and indentation for comparison
- Manual verification of top 10 duplicate patterns confirmed accuracy
- Tool limitations: Runtime import system prevented automated cosine similarity analysis

---

**Recommendation:** Proceed with High Priority consolidations first (iteration module + string helpers + binary search). These provide immediate value with minimal risk.
