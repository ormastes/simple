# Allocator Branch Coverage Analysis

**Module:** `src/std/allocator.spl` (601 LOC)
**Test File:** `test/lib/std/unit/allocator_spec.spl` (455 lines, 55 existing tests)
**Date:** 2026-02-03

---

## Branch Inventory

### ArenaAllocator (Primary Focus - Week 1)

**File:** `src/std/allocator.spl` lines 150-276

#### Critical Branches in `allocate()` (lines 230-254)

1. **Line 242:** `align_up(self.offset, align)`
   - Branch: offset already aligned vs needs padding
   - Test gap: Need explicit test for misalignment scenarios

2. **Line 246:** `if end_offset > self.capacity`
   - **Branch A:** Allocation fits (`end_offset <= self.capacity`)
   - **Branch B:** Arena full (`end_offset > self.capacity`) - returns None
   - Existing coverage: Lines 102-107 test failure case
   - Test gap: Exact fit case (`end_offset == self.capacity`)

3. **Line 247:** `return None`
   - Error path when arena full
   - Existing coverage: Line 106 tests this

4. **Line 254:** `Some(ptr)`
   - Success path
   - Existing coverage: Most tests cover this

#### Additional ArenaAllocator Branches

5. **Line 227:** `self.offset >= self.capacity` (is_full)
   - Existing coverage: Line 112 tests this

6. **Line 219:** `self.capacity - self.offset` (remaining)
   - Existing coverage: Multiple tests verify this

7. **Line 269-271:** `reallocate()` - Optional chaining with `?`
   - Branch A: new allocation succeeds
   - Branch B: new allocation fails (propagates None)
   - Test gap: Need test for reallocate failure

### PoolAllocator Branches

**File:** `src/std/allocator.spl` lines 278-400 (estimated)

Key Branches:
1. Size match check (`size == self.object_size`)
2. Free list empty vs has items
3. Deallocation adds to free list
4. Pool exhaustion
5. Reuse from free list

Existing Coverage: Lines 149-241 (good coverage, but needs verification)

### SlabAllocator Branches

**File:** `src/std/allocator.spl` lines 400-500 (estimated)

Key Branches:
1. Size class selection (8 classes)
2. Allocation from correct slab
3. Fallback to system allocator for oversized
4. Multiple slabs management

Existing Coverage: Lines 246-294 (good coverage)

### SystemAllocator Branches

**File:** `src/std/allocator.spl` lines 97-145

Key Branches:
1. **Line 125:** `if ptr_is_null(ptr)` in allocate
   - Branch A: allocation succeeds (returns Some)
   - Branch B: allocation fails (returns None)

2. **Line 137:** `if ptr_is_null(new_ptr)` in reallocate
   - Branch A: reallocation succeeds
   - Branch B: reallocation fails

Existing Coverage: Lines 13-63 (basic coverage)
Test Gap: Allocation failure scenarios (OOM simulation)

---

## Coverage Gaps - Priority Order

### High Priority (Write This Week)

1. **ArenaAllocator alignment padding**
   ```simple
   # Uncovered: offset misaligned, needs padding calculation
   it "should add alignment padding when offset misaligned":
       val arena = ArenaAllocator(capacity: 256)
       arena.allocate(10, 8)  # offset = 10
       val ptr = arena.allocate(10, 16)  # needs padding to align to 16
       expect ptr.? to_be_true
   ```

2. **ArenaAllocator exact fit**
   ```simple
   # Uncovered: end_offset exactly equals capacity
   it "should allocate when exactly filling arena":
       val arena = ArenaAllocator(capacity: 100)
       val ptr = arena.allocate(100, 8)
       expect ptr.? to_be_true
       expect arena.remaining() to_equal 0
   ```

3. **ArenaAllocator reallocate failure**
   ```simple
   # Uncovered: reallocate when arena can't fit new size
   it "should return None when reallocate fails":
       val arena = ArenaAllocator(capacity: 200)
       val ptr1 = arena.allocate(100, 8)
       if ptr1.?:
           # Try to reallocate to 150 bytes (would need 250 total)
           val ptr2 = arena.reallocate(ptr1.unwrap(), 100, 150, 8)
           expect ptr2.? to_be_false  # Should fail
   ```

4. **PoolAllocator size mismatch**
   - Existing test at line 175-178, verify coverage

5. **PoolAllocator free list reuse**
   - Existing test at 181-196, verify correct branch coverage

6. **SlabAllocator size class boundaries**
   ```simple
   # Test all 8 size class boundaries
   # 16, 32, 64, 128, 256, 512, 1024, 2048
   it "should select correct class for boundary sizes":
       val slab = SlabAllocator()
       # Test each boundary
       expect slab.find_size_class(15) to_equal 0  # 16-byte class
       expect slab.find_size_class(16) to_equal 0  # exact
       expect slab.find_size_class(17) to_equal 1  # 32-byte class
   ```

7. **SlabAllocator oversized fallback**
   - Existing test at line 284-287, verify system allocator path

### Medium Priority

8. **Arena alignment edge cases**
   - Zero size allocation
   - Maximum alignment (e.g., 256, 512)
   - Power-of-2 validation

9. **Pool allocation patterns**
   - Allocate all → deallocate all → reallocate all
   - Interleaved allocate/deallocate
   - Stress test (1000s of operations)

10. **Slab interaction between classes**
    - Allocate from multiple classes
    - Verify independence
    - Memory not shared between classes

### Low Priority (Nice to Have)

11. **Performance characteristics**
    - Measure Arena O(1) allocation
    - Measure Pool free list performance
    - Slab vs System for large allocations

12. **Error conditions**
    - Invalid alignment (not power of 2)
    - Negative sizes (type system prevents, but verify)
    - Double free (undefined behavior, document only)

---

## Test Writing Plan - First 10 Tests

### Test 1: Arena alignment padding (HIGH)
**Branch:** Line 242 - `align_up()` when offset misaligned
**File:** `test/lib/std/unit/allocator_spec.spl`
**Location:** After line 123 (in ArenaAllocator reset context)

```simple
describe "ArenaAllocator":
    context "alignment handling":
        it "should add padding when offset is misaligned":
            val arena = ArenaAllocator(capacity: 256)

            # First allocation: offset = 10 (not aligned to 16)
            val ptr1 = arena.allocate(10, 8)
            expect self.offset to_equal 10

            # Second allocation needs 16-byte alignment
            # Should align 10 → 16, then allocate
            val ptr2 = arena.allocate(10, 16)
            expect ptr2.? to_be_true

            # Total used: 10 (first) + 6 (padding) + 10 (second) = 26
            expect arena.total_allocated() to_equal 20  # Only counts actual data
```

### Test 2: Arena exact capacity fit (HIGH)
**Branch:** Line 246 - `end_offset == self.capacity`

```simple
        it "should succeed when allocation exactly fills arena":
            val arena = ArenaAllocator(capacity: 128)
            val ptr = arena.allocate(128, 8)

            expect ptr.? to_be_true
            expect arena.remaining() to_equal 0
            expect arena.is_full() to_be_true
```

### Test 3: Arena reallocate failure (HIGH)
**Branch:** Line 269 - `?` operator propagates None

```simple
    context "reallocation":
        it "should return None when new size doesn't fit":
            val arena = ArenaAllocator(capacity: 150)

            # Allocate 100 bytes
            val ptr1 = arena.allocate(100, 8)
            expect ptr1.? to_be_true

            # Try to reallocate to 100 bytes (total would be 200)
            if ptr1.?:
                val ptr2 = arena.reallocate(ptr1.unwrap(), 100, 100, 8)
                expect ptr2.? to_be_false
```

### Test 4-6: Pool allocator verification
**Verify existing tests actually cover branches**

### Test 7-8: Slab size class boundaries
**Branch:** Slab `find_size_class()` decision tree

### Test 9-10: SystemAllocator edge cases
**Branch:** Lines 125, 137 - null pointer checks

---

## Verification Commands

```bash
# 1. Run allocator tests with coverage
SIMPLE_COVERAGE=1 simple test test/lib/std/unit/allocator_spec.spl

# 2. Check coverage data
simple spl-coverage status

# 3. Save baseline
simple spl-coverage dump > doc/coverage/allocator_baseline.sdn

# 4. After writing tests, save iteration
simple spl-coverage dump > doc/coverage/allocator_iter1.sdn

# 5. Compare (manual diff)
diff doc/coverage/allocator_baseline.sdn doc/coverage/allocator_iter1.sdn
```

---

## Expected Outcomes - Week 1

| Metric | Baseline | After 10 Tests | After 40 Tests |
|--------|----------|----------------|----------------|
| Total Tests | 55 | 65 | 95 |
| Branch Coverage | ~60% (est) | ~75% | 100% |
| Line Coverage | ~80% (est) | ~90% | 100% |
| Uncovered Branches | ~32 | ~20 | 0 |

---

## Next Steps

1. **TODAY:** Write tests 1-3 (alignment, exact fit, reallocate failure)
2. **Tomorrow:** Write tests 4-10, verify coverage increase
3. **This Week:** Complete remaining 30 tests for 100% allocator coverage
4. **Next Week:** Start GC module (Week 2)

---

**References:**
- Source: `src/std/allocator.spl`
- Tests: `test/lib/std/unit/allocator_spec.spl`
- Coverage: `doc/coverage/COVERAGE_PLAN_STATUS.md`
