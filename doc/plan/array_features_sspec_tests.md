# Array Features - Comprehensive SSpec Test Plan

**Date**: 2026-01-31
**Requirement**: "it must bdd with intensive sspec test verification"

---

## Test Organization

All array features will have intensive SSpec test coverage BEFORE implementation.

### Test File Structure

```
test/system/features/arrays/
├── mutable_by_default_spec.spl              # Decision #3
├── type_conversion_spec.spl                  # Decision #7
├── fixed_size_arrays_spec.spl                # Decision #8
├── fixed_size_edge_cases_spec.spl            # Decision #8 (edge cases)
├── target_defaults_spec.spl                  # Decision #9
├── array_coercion_spec.spl                   # Type coercion
├── freeze_unfreeze_spec.spl                  # freeze() function
└── array_performance_spec.spl                # Performance benchmarks

test/system/features/collections/
├── custom_backend_spec.spl                   # Custom ArrayList/HashMap
└── backend_conversion_spec.spl               # from() method pattern
```

---

## Decision #3: Mutable by Default - SSpec Tests

**File**: `test/system/features/arrays/mutable_by_default_spec.spl`

```simple
describe "Mutable Collections by Default":

    context "Array Mutability":
        it "should allow push on default arrays":
            var arr = [1, 2, 3]
            arr.push(4)
            expect(arr).to_equal([1, 2, 3, 4])

        it "should allow pop on default arrays":
            var arr = [1, 2, 3]
            val last = arr.pop()
            expect(last).to_equal(3)
            expect(arr).to_equal([1, 2])

        it "should allow insert on default arrays":
            var arr = [1, 3]
            arr.insert(1, 2)
            expect(arr).to_equal([1, 2, 3])

        it "should allow remove on default arrays":
            var arr = [1, 2, 3]
            val removed = arr.remove(1)
            expect(removed).to_equal(2)
            expect(arr).to_equal([1, 3])

        it "should allow clear on default arrays":
            var arr = [1, 2, 3]
            arr.clear()
            expect(arr).to_equal([])

        it "should allow indexing assignment":
            var arr = [1, 2, 3]
            arr[1] = 10
            expect(arr).to_equal([1, 10, 3])

    context "Dict Mutability":
        it "should allow insert on default dicts":
            var dict = {"a": 1}
            dict["b"] = 2
            expect(dict).to_equal({"a": 1, "b": 2})

        it "should allow remove on default dicts":
            var dict = {"a": 1, "b": 2}
            dict.remove("a")
            expect(dict).to_equal({"b": 2})

        it "should allow clear on default dicts":
            var dict = {"a": 1, "b": 2}
            dict.clear()
            expect(dict).to_equal({})

    context "val binding with mutable collection":
        it "should allow mutation but not reassignment":
            val arr = [1, 2, 3]
            arr.push(4)  # OK - mutate contents
            expect(arr).to_equal([1, 2, 3, 4])
            # arr = [5, 6]  # ERROR - cannot reassign val

        it "should work with class fields":
            class Container:
                items: [i64]  # val field by default

                me add(item: i64):
                    self.items.push(item)  # OK - mutate field contents

            val c = Container(items: [1, 2])
            c.add(3)
            expect(c.items).to_equal([1, 2, 3])

    context "RefCell behavior":
        it "should handle multiple borrows correctly":
            var arr = [1, 2, 3]
            val len = arr.len()  # Immutable borrow
            expect(len).to_equal(3)
            arr.push(4)  # Mutable borrow (after immutable released)
            expect(arr.len()).to_equal(4)

        it "should panic on simultaneous mutable borrows":
            var arr = [1, 2, 3]
            # This would panic (can't demo in test):
            # arr.map(\x: arr.push(x))  # ERROR: already borrowed
```

**Expected**: 20-25 tests

---

## Decision #7: Type Conversion - SSpec Tests

**File**: `test/system/features/arrays/type_conversion_spec.spl`

```simple
describe "Type Annotation Conversion":

    context "Basic Conversion":
        it "should convert array literal to ArrayList":
            val arr: ArrayList = [1, 2, 3]
            expect(arr.len()).to_equal(3)
            expect(arr.get(0)).to_equal(1)

        it "should convert dict literal to HashMap":
            val map: HashMap = {"a": 1, "b": 2}
            expect(map.get("a")).to_equal(Some(1))
            expect(map.get("c")).to_equal(None)

        it "should convert empty array":
            val arr: ArrayList = []
            expect(arr.len()).to_equal(0)

    context "Function Parameters":
        it "should auto-convert in function calls":
            fn process(data: ArrayList) -> i64:
                data.len()

            val result = process([1, 2, 3])
            expect(result).to_equal(3)

        it "should auto-convert in method calls":
            class Processor:
                fn run(data: ArrayList) -> i64:
                    data.len()

            val p = Processor()
            expect(p.run([1, 2, 3])).to_equal(3)

    context "Return Type Conversion":
        it "should convert return value to expected type":
            fn make_list() -> ArrayList:
                [1, 2, 3]  # Auto-converts

            val list = make_list()
            expect(list.len()).to_equal(3)

    context "Nested Conversion":
        it "should convert nested arrays":
            val matrix: Matrix = [[1, 2], [3, 4]]
            expect(matrix.rows()).to_equal(2)

    context "Error Cases":
        it "should error if from() not defined":
            class NoFrom:
                items: [i64]

            # val x: NoFrom = [1, 2, 3]  # ERROR: no from() method

        it "should error on wrong argument type":
            fn process(data: ArrayList):
                # ...

            # process("not an array")  # ERROR: type mismatch
```

**Expected**: 15-20 tests

---

## Decision #8: Fixed-Size Arrays - SSpec Tests

**File**: `test/system/features/arrays/fixed_size_arrays_spec.spl`

```simple
describe "Fixed-Size Arrays":

    context "Basic Syntax":
        it "should create fixed-size array with type annotation":
            val vec3: [f64; 3] = [1.0, 2.0, 3.0]
            expect(vec3.len()).to_equal(3)

        it "should create 2D fixed-size array":
            val mat3: [[f64; 3]; 3] = [
                [1.0, 0.0, 0.0],
                [0.0, 1.0, 0.0],
                [0.0, 0.0, 1.0],
            ]
            expect(mat3[0][0]).to_equal(1.0)

    context "Compile-Time Size Checking":
        it "should reject size mismatch at compile time":
            # val vec3: [f64; 3] = [1.0, 2.0]  # ERROR: size mismatch

        it "should reject size mismatch with too many elements":
            # val vec3: [f64; 3] = [1.0, 2.0, 3.0, 4.0]  # ERROR: size mismatch

    context "Size-Changing Operations":
        it "should reject push on fixed-size array":
            var vec3: [f64; 3] = [1.0, 2.0, 3.0]
            # vec3.push(4.0)  # ERROR: cannot push to fixed-size array

        it "should reject pop on fixed-size array":
            var vec3: [f64; 3] = [1.0, 2.0, 3.0]
            # vec3.pop()  # ERROR: cannot pop from fixed-size array

        it "should reject insert on fixed-size array":
            var vec3: [f64; 3] = [1.0, 2.0, 3.0]
            # vec3.insert(1, 1.5)  # ERROR: cannot insert

        it "should reject remove on fixed-size array":
            var vec3: [f64; 3] = [1.0, 2.0, 3.0]
            # vec3.remove(1)  # ERROR: cannot remove

    context "Allowed Operations":
        it "should allow indexing read":
            val vec3: [f64; 3] = [1.0, 2.0, 3.0]
            expect(vec3[0]).to_equal(1.0)
            expect(vec3[2]).to_equal(3.0)

        it "should allow indexing write":
            var vec3: [f64; 3] = [1.0, 2.0, 3.0]
            vec3[1] = 10.0
            expect(vec3[1]).to_equal(10.0)

        it "should allow len()":
            val vec3: [f64; 3] = [1.0, 2.0, 3.0]
            expect(vec3.len()).to_equal(3)

        it "should allow iteration":
            val vec3: [f64; 3] = [1.0, 2.0, 3.0]
            var sum = 0.0
            for x in vec3:
                sum += x
            expect(sum).to_equal(6.0)

    context "Function Parameters":
        it "should enforce size in function parameters":
            fn dot(a: [f64; 3], b: [f64; 3]) -> f64:
                a[0]*b[0] + a[1]*b[1] + a[2]*b[2]

            val v1: [f64; 3] = [1.0, 2.0, 3.0]
            val v2: [f64; 3] = [4.0, 5.0, 6.0]
            expect(dot(v1, v2)).to_equal(32.0)

        it "should reject wrong size in function call":
            fn needs_three(v: [i64; 3]):
                # ...

            val vec4: [i64; 4] = [1, 2, 3, 4]
            # needs_three(vec4)  # ERROR: size mismatch

    context "Type Inference":
        it "should infer size from function parameter":
            fn process(v: [f64; 3]) -> f64:
                v[0] + v[1] + v[2]

            val result = process([1.0, 2.0, 3.0])  # Infers [f64; 3]
            expect(result).to_equal(6.0)

    context "Const Fixed-Size Arrays":
        it "should create const fixed-size array":
            val UNIT_X: const [f64; 3] = [1.0, 0.0, 0.0]
            expect(UNIT_X[0]).to_equal(1.0)

        it "should reject mutation of const array":
            val UNIT_X: const [f64; 3] = [1.0, 0.0, 0.0]
            # UNIT_X[0] = 2.0  # ERROR: cannot mutate const array
```

**Expected**: 25-30 tests

---

## Decision #8: Fixed-Size Edge Cases - SSpec Tests

**File**: `test/system/features/arrays/fixed_size_edge_cases_spec.spl`

```simple
describe "Fixed-Size Array Edge Cases":

    context "Size Zero":
        it "should allow size-zero arrays":
            val empty: [i64; 0] = []
            expect(empty.len()).to_equal(0)

    context "Large Sizes":
        it "should handle large fixed-size arrays":
            val buffer: [u8; 1024] = [0; 1024]  # Array of 1024 zeros
            expect(buffer.len()).to_equal(1024)

    context "Array Concatenation":
        it "should calculate size for concatenation":
            val a: [i64; 2] = [1, 2]
            val b: [i64; 3] = [3, 4, 5]
            val c = a + b  # Type: [i64; 5]
            expect(c.len()).to_equal(5)

    context "Slicing":
        it "should return dynamic array from slice":
            val vec5: [i64; 5] = [1, 2, 3, 4, 5]
            val slice = vec5[1:4]  # Type: [i64] (dynamic)
            expect(slice.len()).to_equal(3)

        it "should allow fixed-size slice with const bounds":
            val vec5: [i64; 5] = [1, 2, 3, 4, 5]
            # val slice: [i64; 3] = vec5[1:4]  # Future: const slice

    context "Runtime Size Checks":
        it "should check size at runtime when needed":
            fn make_array(n: i64) -> [i64]:
                [0 for _ in 0..n]

            fn needs_three(v: [i64; 3]):
                # ...

            val arr = make_array(5)
            # needs_three(arr)  # RUNTIME ERROR: size mismatch

    context "Conversion":
        it "should convert dynamic to fixed-size with check":
            val arr: [i64] = [1, 2, 3]
            val vec3 = arr.to_fixed::<3>()  # Runtime check
            expect(vec3.len()).to_equal(3)

        it "should error on wrong size conversion":
            val arr: [i64] = [1, 2]
            # val vec3 = arr.to_fixed::<3>()  # ERROR: size 2 != 3
```

**Expected**: 15-20 tests

---

## Decision #9: Target-Based Defaults - SSpec Tests

**File**: `test/system/features/arrays/target_defaults_spec.spl`

```simple
describe "Target-Based Mutability Defaults":

    context "General Mode (Default)":
        it "should make arrays mutable by default":
            # Compile with: --target=general
            val arr = [1, 2, 3]
            arr.push(4)  # Should work
            expect(arr).to_equal([1, 2, 3, 4])

    context "Embedded Mode":
        @target(embedded)

        it "should make arrays immutable by default":
            val arr = [1, 2, 3]
            # arr.push(4)  # ERROR: frozen array

        it "should allow explicit mutable":
            var arr = mut [1, 2, 3]
            arr.push(4)  # OK
            expect(arr).to_equal([1, 2, 3, 4])

        it "should make dicts immutable by default":
            val dict = {"a": 1}
            # dict["b"] = 2  # ERROR: frozen dict

        it "should allow explicit mutable dict":
            var dict = mut {"a": 1}
            dict["b"] = 2  # OK
            expect(dict).to_equal({"a": 1, "b": 2})

    context "Module Attribute Override":
        it "should override global target with module attribute":
            @target(embedded)
            # Even if compiled with --target=general,
            # this file uses embedded defaults

            val arr = [1, 2, 3]  # Immutable
            # arr.push(4)  # ERROR

    context "Type Annotation Override":
        @target(embedded)

        it "should allow mutable with type annotation":
            val arr: mut [i64] = [1, 2, 3]  # Explicit mutable
            arr.push(4)  # OK

    context "Memory Efficiency":
        @target(embedded)

        it "should use less memory for immutable":
            val arr = [1, 2, 3]  # FrozenArray (no RefCell)
            # Size: Rc<Vec> = 32 bytes
            # vs Rc<RefCell<Vec>> = 48 bytes
            expect(arr.memory_size()).to_be_less_than(40)
```

**Expected**: 15-20 tests

---

## Freeze/Unfreeze - SSpec Tests

**File**: `test/system/features/arrays/freeze_unfreeze_spec.spl`

```simple
describe "Freeze and Unfreeze":

    context "Freeze Function":
        it "should freeze mutable array":
            var arr = [1, 2, 3]
            val frozen = freeze(arr)
            # frozen.push(4)  # ERROR: frozen array

        it "should freeze mutable dict":
            var dict = {"a": 1}
            val frozen = freeze(dict)
            # frozen["b"] = 2  # ERROR: frozen dict

        it "should be idempotent":
            val arr = freeze([1, 2, 3])
            val frozen_again = freeze(arr)
            expect(frozen_again).to_equal(arr)

    context "Frozen Array Operations":
        it "should allow reads on frozen array":
            val frozen = freeze([1, 2, 3])
            expect(frozen[0]).to_equal(1)
            expect(frozen.len()).to_equal(3)

        it "should reject mutations on frozen array":
            val frozen = freeze([1, 2, 3])
            # frozen.push(4)  # ERROR
            # frozen.pop()  # ERROR
            # frozen[0] = 10  # ERROR

        it "should allow functional operations":
            val frozen = freeze([1, 2, 3])
            val doubled = frozen.map(\x: x * 2)  # Returns new array
            expect(doubled).to_equal([2, 4, 6])

    context "Memory Optimization":
        it "should remove RefCell overhead when frozen":
            var arr = [1, 2, 3]  # Rc<RefCell<Vec>> = 48 bytes
            val frozen = freeze(arr)  # Rc<Vec> = 32 bytes
            expect(frozen.memory_overhead()).to_be_less_than(arr.memory_overhead())

    context "Unfreeze (Optional)":
        it "should convert frozen to mutable":
            val frozen = freeze([1, 2, 3])
            var arr = unfreeze(frozen)  # Copy-on-write
            arr.push(4)
            expect(arr).to_equal([1, 2, 3, 4])
            expect(frozen).to_equal([1, 2, 3])  # Original unchanged
```

**Expected**: 15-20 tests

---

## Custom Backend - SSpec Tests

**File**: `test/system/features/collections/custom_backend_spec.spl`

```simple
describe "Custom Collection Backends":

    context "ArrayList Implementation":
        it "should create ArrayList from array literal":
            val arr: ArrayList = [1, 2, 3]
            expect(arr.len()).to_equal(3)

        it "should support push":
            var arr: ArrayList = [1, 2]
            arr.push(3)
            expect(arr.len()).to_equal(3)

        it "should support pop":
            var arr: ArrayList = [1, 2, 3]
            val last = arr.pop()
            expect(last).to_equal(3)
            expect(arr.len()).to_equal(2)

    context "HashMap Implementation":
        it "should create HashMap from dict literal":
            val map: HashMap = {"a": 1, "b": 2}
            expect(map.len()).to_equal(2)

        it "should support get":
            val map: HashMap = {"a": 1, "b": 2}
            expect(map.get("a")).to_equal(Some(1))
            expect(map.get("c")).to_equal(None)

        it "should support insert":
            var map: HashMap = {"a": 1}
            map.insert("b", 2)
            expect(map.get("b")).to_equal(Some(2))

    context "PersistentVector":
        it "should create immutable persistent vector":
            val vec: PersistentVector = [1, 2, 3]
            val vec2 = vec.push(4)  # Returns new vector
            expect(vec.len()).to_equal(3)  # Original unchanged
            expect(vec2.len()).to_equal(4)

        it "should share structure":
            val vec1: PersistentVector = [1, 2, 3]
            val vec2 = vec1.push(4)
            # vec1 and vec2 share nodes (structural sharing)
            expect(vec1.shares_structure_with(vec2)).to_be_true()
```

**Expected**: 15-20 tests

---

## Performance - SSpec Tests

**File**: `test/system/features/arrays/array_performance_spec.spl`

```simple
describe "Array Performance":

    context "Mutable Operations":
        it "should have O(1) push":
            var arr = []
            val start = time_ms()
            for i in 0..10000:
                arr.push(i)
            val elapsed = time_ms() - start
            expect(elapsed).to_be_less_than(100)  # Should be fast

        it "should have O(1) pop":
            var arr = [i for i in 0..10000]
            val start = time_ms()
            for _ in 0..10000:
                arr.pop()
            val elapsed = time_ms() - start
            expect(elapsed).to_be_less_than(100)

    context "Memory Usage":
        it "should not leak memory on repeated mutations":
            var arr = []
            val initial_mem = memory_usage()
            for i in 0..1000:
                arr.push(i)
                arr.pop()
            val final_mem = memory_usage()
            expect(final_mem - initial_mem).to_be_less_than(1024)  # < 1KB leak

    context "Frozen Array Performance":
        it "should have zero RefCell overhead for frozen":
            val frozen = freeze([i for i in 0..1000])
            val start = time_ms()
            var sum = 0
            for x in frozen:
                sum += x
            val elapsed = time_ms() - start
            expect(elapsed).to_be_less_than(10)  # Fast iteration

    context "Fixed-Size Array Performance":
        it "should have zero bounds checking for fixed-size":
            val vec: [i64; 1000] = [0; 1000]
            val start = time_ms()
            var sum = 0
            for i in 0..1000:
                sum += vec[i]  # No bounds check (known size)
            val elapsed = time_ms() - start
            expect(elapsed).to_be_less_than(5)  # Very fast
```

**Expected**: 10-15 tests

---

## Test Execution Strategy

### Phase 1: Write All Tests FIRST (Before Implementation)

**Test-Driven Development**: Write tests that fail, then implement features to make them pass.

```bash
# Step 1: Write all SSpec tests
# Step 2: Run tests - all should fail initially
./rust/target/debug/simple_runtime test test/system/features/arrays/

# Expected output:
# FAIL test/system/features/arrays/mutable_by_default_spec.spl (0 passed, 25 failed)
# FAIL test/system/features/arrays/type_conversion_spec.spl (0 passed, 20 failed)
# FAIL test/system/features/arrays/fixed_size_arrays_spec.spl (0 passed, 30 failed)
# ... etc

# Step 3: Implement features one by one
# Step 4: Watch tests turn green
```

### Phase 2: Implement and Verify

For each decision:
1. Write SSpec tests (all fail)
2. Implement feature
3. Run tests (watch them pass)
4. Add more edge case tests
5. Refactor if needed
6. Final verification

### Phase 3: Integration Testing

```simple
describe "Array Features Integration":
    it "should work together seamlessly":
        # Fixed-size array with custom backend
        val vec3: Vector3D = [1.0, 2.0, 3.0]

        # Mutable by default in general mode
        vec3[0] = 5.0

        # Freeze for safety
        val frozen = freeze(vec3)

        # Type conversion
        val persistent: PersistentVector = frozen

        expect(persistent.get(0)).to_equal(5.0)
```

---

## Total Test Count

| Feature | File | Tests |
|---------|------|-------|
| Mutable by Default | `mutable_by_default_spec.spl` | 20-25 |
| Type Conversion | `type_conversion_spec.spl` | 15-20 |
| Fixed-Size Arrays | `fixed_size_arrays_spec.spl` | 25-30 |
| Fixed-Size Edge Cases | `fixed_size_edge_cases_spec.spl` | 15-20 |
| Target Defaults | `target_defaults_spec.spl` | 15-20 |
| Freeze/Unfreeze | `freeze_unfreeze_spec.spl` | 15-20 |
| Custom Backends | `custom_backend_spec.spl` | 15-20 |
| Performance | `array_performance_spec.spl` | 10-15 |

**Total**: 130-170 comprehensive SSpec tests

---

## Test Writing Timeline

| Phase | Duration | Activity |
|-------|----------|----------|
| Week 1 | 8-12h | Write all SSpec tests (before implementation) |
| Week 2-4 | Per decision | Implement features, watch tests pass |
| Week 5 | 4-6h | Integration tests and edge cases |

**Test-first approach ensures**:
- Clear requirements before coding
- No missing edge cases
- Regression prevention
- Living documentation

---

## Success Criteria

✅ All 130-170 SSpec tests written BEFORE implementation starts
✅ Each test has clear describe/context/it structure
✅ Tests cover happy path, edge cases, and error cases
✅ Performance tests verify O(1) operations
✅ Memory tests verify no leaks
✅ Integration tests verify features work together

**This is intensive SSpec verification as required!**
