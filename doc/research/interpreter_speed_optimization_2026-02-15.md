# Interpreter Speed & Startup Optimization Analysis

**Date:** 2026-02-15
**Scope:** Go/Python optimization techniques applied to Simple interpreter
**Status:** Research complete, actionable findings

---

## Executive Summary

Analysis of Go and Python interpreter optimization techniques, cross-referenced with a thorough audit of the Simple interpreter source code (`src/core/interpreter/`). Found **8 critical algorithmic complexity issues** and **12 applicable optimization techniques** from Go/Python.

### Key Findings

| Issue | Current | Optimal | Impact |
|-------|---------|---------|--------|
| Variable lookup | O(depth * vars) | O(1) | **CRITICAL** |
| Function table lookup | O(n) linear | O(1) hash | **CRITICAL** |
| String concat in loops | O(n^2) | O(n) | **HIGH** |
| Scope pop | O(depth) rebuild | O(1) pop | **MEDIUM** |
| JIT call tracking | O(n) linear | O(1) hash | **MEDIUM** |
| Struct field access | O(fields) | O(1) index | **MEDIUM** |
| Range allocation | O(n) array | Lazy iterator | **MEDIUM** |
| Mono cache lookup | O(cache) | O(1) hash | **LOW** |

---

## Part 1: Lessons from Go

### 1.1 Startup Speed

**Go's approach:** Static linking, minimal runtime init, lazy initialization with `sync.Once`.

**Applicable to Simple:**
- **Frozen modules:** Pre-compile `src/std/` modules into bytecode embedded in the 33MB runtime binary. Python 3.11+ does this and achieves 50%+ startup improvement.
- **Lazy standard library:** Only initialize `std.math`, `std.string`, `std.array` when first imported, not at startup.
- **Bytecode caching:** Create `.splc` cache files alongside `.spl` with hash-based invalidation. Skip lexing/parsing when cache is fresh.

### 1.2 Escape Analysis / Stack vs Heap

**Go's approach:** Compiler determines if variables can live on stack (10-100x faster than heap allocation).

**Applicable to Simple:**
- **Value-based AST nodes:** Store small literals (IntLiteral, BoolLiteral) as values in arrays rather than heap-allocated pointers.
- **Stack-based environments:** For function-scoped variables, use fixed-size arrays (`[256]Value`) instead of dynamic maps. Fall back to map only when >256 locals.
- **Pool common values:** Cache `nil`, `true`, `false`, integers 0-255, empty string.

### 1.3 String Interning

**Go 1.23+ `unique.Handle`:** Deduplicate identifier strings so comparison becomes pointer equality O(1) instead of string comparison O(n).

**Applicable to Simple:**
- Intern all variable names, function names, keywords during lexing.
- Symbol table becomes `map[interned_id -> Value]` with integer key hashing (faster than string hashing).
- Name comparison in scope lookup becomes pointer/integer comparison.

### 1.4 Swiss Tables (Go 1.24+)

70% memory reduction and 30% faster lookups for hash maps. Key insight: SIMD-friendly control bytes, quadratic probing reduces clustering.

**Applicable to Simple:**
- Current parallel-array-based lookups are the bottleneck. Even a basic hash map would be a massive improvement over linear scan.

### 1.5 Dispatch Optimization

**Go's approach:** Switch on integer node type compiles to jump table (O(1)) for 8+ cases.

**Applicable to Simple:**
- Currently uses string-based tag matching in `eval_expr`. Integer enum tags with jump table would eliminate string comparison overhead.
- Store function pointers in AST nodes for direct dispatch (no match/switch needed).

### 1.6 Frame Stack Array

**Go's approach:** Goroutines start with 2KB stack, grow dynamically.

**Applicable to Simple:**
- Pre-allocate frame array (256 frames) instead of allocating per function call.
- Reuse frames by maintaining a depth counter.

---

## Part 2: Lessons from Python

### 2.1 Specializing Adaptive Interpreter (PEP 659)

**Python 3.11's approach:** Instructions adapt at runtime based on observed types.
- `BINARY_OP` -> `BINARY_OP_ADD_INT` after observing integer operands.
- 25-50% speedup in real code.

**Applicable to Simple:**
```simple
# After seeing node always gets i64 + i64:
# Replace BinaryOp(Add, left, right) with IntAdd(left, right)
# IntAdd skips type checking and does native i64 add
```

### 2.2 LOAD_FAST: Index-Based Local Variables

**Python's approach:** Local variables stored in contiguous array, accessed by compile-time index. LOAD_FAST (array[index]) is 3-4x faster than LOAD_GLOBAL (dict lookup).

**THIS IS THE SINGLE MOST IMPACTFUL OPTIMIZATION FOR SIMPLE.**

Currently Simple does:
```
env_lookup("count") -> walk scope chain -> linear scan each scope -> string compare
```

Should do:
```
frame.locals[3]  # O(1) array access by pre-computed index
```

### 2.3 Computed Goto Dispatch

**Python's approach:** 15-20% faster than switch dispatch. Each opcode has its own dispatch jump, enabling better branch prediction.

**Applicable to Simple:**
- For tree-walk interpreter, equivalent is storing `eval_fn` pointer in each AST node.
- Avoid the large match/switch in `eval_expr` that dispatches on node tag.

### 2.4 Zero-Cost Exception Handling

**Python 3.11:** Exception metadata in side table, not bytecode. Try blocks have zero overhead when no exception is raised.

**Applicable to Simple:** Since Simple uses the Option pattern (`var error = nil`) instead of exceptions, this is already effectively zero-cost. No change needed.

### 2.5 Frame Optimization (Python 3.11+)

**Python's approach:** Frames allocated in contiguous array on C stack, not heap-allocated objects.

**Applicable to Simple:**
```simple
struct Interpreter:
    frame_stack: [Frame]  # Pre-allocated array of 256 frames
    frame_depth: i64

    fn push_frame():
        val frame = self.frame_stack[self.frame_depth]
        self.frame_depth = self.frame_depth + 1
        frame.reset()  # Reuse, no allocation

    fn pop_frame():
        self.frame_depth = self.frame_depth - 1
```

### 2.6 Compact Dict

**Python 3.6+:** Separate index array from key-value storage. 20-25% memory savings, better cache locality.

**Applicable to Simple:** When implementing hash maps for the fixes below, use compact dict design.

### 2.7 Immortal Objects (Python 3.12+)

**Pre-allocate and reuse:** `nil`, `true`, `false`, small integers. Eliminates allocation/deallocation overhead for the most common values.

**Applicable to Simple (value.spl):**
```simple
# Pre-allocate at startup
val VAL_NIL = val_make_nil_once()
val VAL_TRUE = val_make_bool_once(true)
val VAL_FALSE = val_make_bool_once(false)
val VAL_ZERO = val_make_int_once(0)
val VAL_ONE = val_make_int_once(1)

# In hot paths, return cached value instead of allocating new
fn eval_bool_literal(b: bool) -> i64:
    if b: VAL_TRUE else: VAL_FALSE
```

### 2.8 PyPy Tracing JIT Insights

**Key takeaway:** Profile which code paths are hot, generate specialized versions, use guards to validate assumptions, fall back when guards fail.

**Applicable to Simple:**
- The existing JIT threshold mechanism (`jit.spl`) is the right foundation.
- After threshold is hit, generate specialized AST with type assumptions baked in.
- If type assumption fails at runtime, deoptimize back to generic path.

---

## Part 3: Algorithmic Complexity Audit of Simple Interpreter

### 3.1 CRITICAL: Variable Lookup is O(depth * vars_per_scope)

**File:** `src/core/interpreter/env.spl` lines 112-134

```simple
fn env_lookup(name: text) -> i64:
    var si = env_depth - 1
    for s_names in scope_names:      # O(depth) outer loop
        val names = scope_names[scope_idx]
        var i: i64 = 0
        for n in names:               # O(vars_per_scope) inner loop
            if n == name:
                return values[i]
            i = i + 1
        si = si - 1
    # Then scans globals O(globals)
```

**Problem:** Every variable read/write walks the entire scope chain doing linear string comparisons. For 10 scopes with 20 variables each = 200 string comparisons per variable access.

**Fix (Option A - Hash map per scope):**
```simple
# Use Dict<text, i64> per scope
fn env_lookup(name: text) -> i64:
    var si = env_depth - 1
    while si >= 0:
        val result = scope_maps[si].get(name)  # O(1) hash lookup
        if result != nil: return result
        si = si - 1
    global_map.get(name) ?? -1  # O(1)
```

**Fix (Option B - Index-based, like Python LOAD_FAST):**
```simple
# During parsing, assign each variable an integer index
# At runtime:
fn env_lookup_fast(index: i64) -> i64:
    return frame.locals[index]  # O(1) array access
```

**Estimated speedup:** 10-50x for variable-heavy code.

### 3.2 CRITICAL: Function Table Lookup is O(n)

**File:** `src/core/interpreter/eval.spl` lines 211-217

```simple
fn func_table_lookup(name: text) -> i64:
    var i: i64 = 0
    for fn_name in func_table_names:  # O(n) scan all functions
        if fn_name == name:
            return func_table_decls[i]
        i = i + 1
    -1
```

**Problem:** Every function call scans all registered functions. With 100 functions and 10,000 calls = 1,000,000 string comparisons.

**Fix:** Replace parallel arrays with hash map: `var func_table: Dict<text, i64>`

**Estimated speedup:** 5-20x for function-call-heavy code.

### 3.3 HIGH: String Concatenation in Loops is O(n^2)

**File:** `src/core/interpreter/eval.spl` lines 251-269 (source scanning) and lines 1362-1369 (string interpolation)

```simple
# Source scanning - builds lines by appending chars
current_line = current_line + ch  # O(n^2) - copies entire string each time

# String interpolation
result = result + val_to_text(part_val)  # O(n^2)
```

**Problem:** String `+` creates a new string and copies all previous characters. For N characters/parts, total work is 1 + 2 + 3 + ... + N = O(n^2).

**Fix:** Use array of parts, then join at the end:
```simple
var parts: [text] = []
for part_eid in parts:
    parts.push(val_to_text(eval_expr(part_eid)))
val result = text_join(parts, "")  # Single O(n) concatenation
```

### 3.4 MEDIUM: Scope Pop Rebuilds Entire Stack

**File:** `src/core/interpreter/env.spl` lines 45-57

```simple
fn env_pop_scope():
    # Rebuilds scope_names and scope_values arrays from scratch
    var new_names: [[text]] = []
    var new_values: [[i64]] = []
    var i: i64 = 0
    for names in scope_names:     # O(depth) to copy
        if i < env_depth - 1:
            new_names.push(names)
            new_values.push(scope_values[i])
        i = i + 1
```

**Problem:** Every scope exit (function return, block end) copies the entire scope stack.

**Fix:** Use array `.pop()` or maintain a depth counter without copying:
```simple
fn env_pop_scope():
    scope_names.pop()
    scope_values.pop()
    env_depth = env_depth - 1
```

### 3.5 MEDIUM: JIT Call Tracking is O(n)

**File:** `src/core/interpreter/jit.spl` lines 60-71

```simple
fn jit_record_call(fn_name: text):
    var i: i64 = 0
    for name in jit_call_names:       # O(tracked_functions)
        if name == fn_name:
            jit_call_values[i] = jit_call_values[i] + 1
            return
        i = i + 1
```

**Problem:** Every function call scans the JIT tracking table.

**Fix:** Hash map: `var jit_call_counts: Dict<text, i64>`

### 3.6 MEDIUM: Struct Field Access is O(fields)

**File:** `src/core/interpreter/value.spl` lines 149-157

```simple
fn val_struct_get_field(vid: i64, field_name: text) -> i64:
    val fields = val_struct_fields[vid]
    var i: i64 = 0
    for name in fields:              # O(field_count)
        if name == field_name:
            return values[i]
        i = i + 1
```

**Problem:** Every `.field` access scans all fields.

**Fix (Option A):** Hash map per struct instance.
**Fix (Option B):** Compile-time field indices (like Python's `__slots__`). Store field offset in AST node.

### 3.7 MEDIUM: Range Allocates Full Array

**File:** `src/core/interpreter/eval.spl` lines 708-733

```simple
fn eval_range(eid: i64) -> i64:
    var elements: [i64] = []
    var current = start_n
    # Allocates val_make_int for EVERY integer in range
    for _unused in func_table_names:
        elements.push(val_make_int(current))
        current = current + 1
```

**Problem:** `for i in 0..10000` allocates 10,000 value nodes upfront.

**Fix:** Lazy range iterator that yields values on demand.

### 3.8 LOW: Struct/Mono Cache Lookups are O(n)

Similar parallel-array linear scan patterns in:
- `struct_table_lookup` (eval.spl:358-364)
- `mono_cache_lookup` (eval.spl:66-73)
- `must_use_is_registered` (eval.spl:236-246)

All should use hash maps.

### 3.9 ADDITIONAL: Lexer Character Classification

**File:** `src/core/lexer.spl` lines 40-56

```simple
fn is_digit(c: text) -> bool:
    DIGITS.contains(c)  # O(10) string contains
```

**Fix:** Use ASCII range check: `c >= "0" and c <= "9"` (O(1) comparison).

---

## Part 4: Prioritized Optimization Plan

### Phase 1: Hash Map Conversions (Highest Impact, Lowest Risk) -- IMPLEMENTED

| Target | File | Current | Status |
|--------|------|---------|--------|
| Function lookup | eval.spl | O(n) -> O(1) hash | DONE |
| Variable lookup | env.spl | O(depth*vars) -> O(1) per scope | DONE |
| Struct lookup | eval.spl | O(n) -> O(1) hash | DONE |
| JIT tracking | jit.spl | O(n) -> O(1) hash | DONE |
| Mono cache | eval.spl | O(n) -> O(1) hash | DONE |
| Must-use registry | eval.spl | O(n) -> O(1) hash | DONE |
| Return type table | eval.spl | O(n) -> O(1) hash | DONE |
| Scope pop | env.spl | O(depth) rebuild -> O(1) decrement | DONE |

Shared hash utility: `src/core/interpreter/hashmap.spl` (64 lines)

### Phase 2: String Optimization -- IMPLEMENTED

| Target | File | Current | Status |
|--------|------|---------|--------|
| Source scanning | eval.spl | O(n^2) -> O(n) slice-based | DONE |
| Line trimming | eval.spl | O(n^2) -> O(n) slice-based | DONE |
| Lexer char classification | lexer.spl | O(k) contains -> O(1) range check | DONE |
| String interpolation | eval.spl | O(n^2) but parts typically small | SKIPPED (low impact) |
| Identifier interning | lexer.spl | No interning | NOT DONE (Phase 4 prerequisite) |

### Phase 3: Allocation Reduction -- IMPLEMENTED

| Target | File | Current | Status |
|--------|------|---------|--------|
| Value caching | value.spl | Alloc every literal -> cached nil/true/false/0-255/"" | DONE |
| Frame reuse | env.spl | Rebuild on pop -> O(1) slot reuse | DONE (Phase 1) |
| Range iterator | eval.spl | eval_for_expr already lazy | DONE (cache helps 0-255) |
| Struct field access | value.spl | O(fields) linear | SKIPPED (2-5 fields typical, hash overhead not worth it) |

### Phase 4: Advanced (Index-Based Access) -- NOT IMPLEMENTED

| Target | File | Current | Expected Speedup |
|--------|------|---------|-----------------|
| Local var indexing | parser.spl + env.spl | Name lookup | 10-50x |
| Field indexing | parser.spl + value.spl | Name lookup | 5-10x |
| Specialized nodes | eval.spl | Generic eval | 25-50% |

Requires parser changes to assign compile-time indices. High complexity/risk.

---

## Part 5: Comparison Table

| Technique | Go | Python | Simple (Before) | Simple (After) | Status |
|-----------|-----|--------|-----------------|----------------|--------|
| Variable lookup | Compile-time offset | LOAD_FAST (index) | O(depth*vars) linear | O(1) hash per scope | DONE |
| Function dispatch | Interface + itab cache | Specializing adaptive | O(n) linear scan | O(1) hash map | DONE |
| String interning | unique.Handle (1.23+) | PyUnicode_InternInPlace | None | Not yet | TODO |
| GC/Memory | Concurrent mark-sweep | Refcount + gen GC | N/A (manual) | Immortal cache (260 values) | DONE |
| Dispatch | Jump table (8+ cases) | Computed goto (15-20%) | match on string tag | Same (string tag) | TODO |
| Frame alloc | 2KB goroutine stack | Stack array (3.11+) | Rebuild on pop | O(1) slot reuse | DONE |
| Common values | Stack alloc small objs | Free lists + immortal | Alloc every time | Cached nil/true/false/0-255/"" | DONE |
| Hash maps | Swiss tables (1.24+) | Compact dict (3.6+) | Parallel arrays | Chained hash maps | DONE |
| Char classification | N/A | N/A | O(k) contains() | O(1) range compare | DONE |

---

## References

### Go
- [Go Escape Analysis](https://goperf.dev/01-common-patterns/stack-alloc/)
- [Swiss Tables in Go 1.24](https://go.dev/blog/swisstable)
- [Go String Interning](https://go.dev/blog/unique)
- [Go Interface Devirtualization](https://www.polarsignals.com/blog/posts/2023/11/24/go-interface-devirtualization-and-pgo)
- [Go Startup Speed](https://eblog.fly.dev/startfast.html)
- [Go Bounds Check Elimination](https://www.ardanlabs.com/blog/2018/04/bounds-check-elimination-in-go.html)
- [Go Green Tea GC](https://go.dev/blog/greenteagc)

### Python
- [PEP 659 - Specializing Adaptive Interpreter](https://peps.python.org/pep-0659/)
- [Python Variable Implementation](https://tenthousandmeters.com/blog/python-behind-the-scenes-5-how-variables-are-implemented-in-cpython/)
- [Python 3.13 JIT (PEP 744)](https://peps.python.org/pep-0744/)
- [CPython Compact Dict](https://github.com/python/cpython/commit/742da040db28e1284615e88874d5c952da80344e)
- [PEP 683 - Immortal Objects](https://peps.python.org/pep-0683/)
- [Computed Goto Dispatch](https://eli.thegreenplace.net/2012/07/12/computed-goto-for-efficient-dispatch-tables)
- [CPython String Interning](https://github.com/python/cpython/blob/main/InternalDocs/string_interning.md)

### Interpreter Design
- [AST vs Bytecode Interpreters](https://stefan-marr.de/2023/10/ast-vs-bytecode-interpreters/)
- [AST Node Merging](https://2022.programming-conference.org/details/MoreVMs-2022-papers/3/Less-Is-More-Merging-AST-Nodes-To-Optimize-Interpreters)
- [Self-Optimizing AST Interpreters](https://dl.acm.org/doi/10.1145/2384577.2384587)
- [Data Locality Patterns](https://gameprogrammingpatterns.com/data-locality.html)
