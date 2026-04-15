# Set Literal `s{}` Completion Plan

**Feature:** Complete set literal `s{}` syntax implementation
**Status:** Partially implemented (parser done, MIR lowering incomplete)
**Impact:** 2 skipped tests
**Estimated Effort:** 1-2 days

---

## Current Status

### ✅ Completed Components

1. **Lexer** (`src/compiler/lexer.spl`)
   - `SetLitStart` token type
   - Recognizes `s{` pattern
   - Priority handling (literals before blocks)

2. **Parser** (`src/compiler/parser.spl`)
   - `parse_set_literal()` - Parses `s{elem1, elem2, ...}`
   - `parse_set_literal_after_s()` - Handles `s` identifier followed by `{`
   - AST node: `ExprKind.SetLit([Expr])`

3. **HIR** (`src/compiler/hir_definitions.spl`)
   - `HirExprKind.SetLit(elements: [HirExpr], elem_type: HirType?)`
   - Type inference support

4. **Standard Library** (`src/lib/src/set.spl`)
   - Full `Set<T>` implementation with all methods
   - `Set.new()`, `insert()`, `has()`, `union()`, `intersect()`, etc.
   - 498 lines, production-ready

### ❌ Incomplete Components

1. **MIR Lowering** (`src/compiler/mir_lowering.spl:682-708`)
   - Function `lower_set_lit()` exists but has TODO comments
   - Doesn't emit actual `Set.new()` call
   - Doesn't emit `insert()` calls for elements
   - Returns empty temp local instead of populated set

---

## The Problem

**Current code (line 682-708):**

```simple
me lower_set_lit(elements: [HirExpr]) -> LocalId:
    """Lower set literal to Set.new() + insert() calls."""
    val elem_type = MirType__i64()
    val set_type = MirType(kind: MirTypeKind.Named("Set", [elem_type]))

    # Generate: val set = Set.new()
    val set_local = self.builder.new_temp(set_type)
    # TODO: Emit StaticCall to Set.new() - for now just allocate temp
    # self.builder.emit_static_call(set_local, "Set", "new", [])

    # Generate: set.insert(elem) for each element
    for element in elements:
        val elem_local = self.lower_expr(element)
        # TODO: Emit MethodCall to set.insert(elem)
        # val insert_result = self.builder.new_temp(MirType__bool())
        # self.builder.emit_method_call(insert_result, set_local, "insert", [elem_local])

    set_local  # Returns uninitialized temp!
```

**What it should do:**

Transform `s{1, 2, 3}` into equivalent of:
```simple
val set = Set.new()
set.insert(1)
set.insert(2)
set.insert(3)
set  # Return the populated set
```

---

## Solution: Complete MIR Lowering

### Step 1: Emit `Set.new()` Call

```simple
me lower_set_lit(elements: [HirExpr]) -> LocalId:
    # Infer element type from first element (or use type param)
    val elem_type = if elements.len() > 0:
        self.infer_expr_type(elements[0])
    else:
        MirType__i64()  # Default for empty sets

    val set_type = MirType(kind: MirTypeKind.Named("Set", [elem_type]))

    # 1. Call Set.new() -> returns Set<T>
    val set_new_symbol = self.resolve_static_method("Set", "new")
    val set_new_operand = self.symbol_to_operand(set_new_symbol)
    val set_local = self.builder.emit_call(
        set_new_operand,
        [],  # No arguments
        set_type
    )
```

### Step 2: Emit `insert()` Calls

```simple
    # 2. For each element, call set.insert(elem)
    for element in elements:
        val elem_local = self.lower_expr(element)

        # Resolve insert method on Set<T>
        val insert_symbol = self.resolve_method(set_type, "insert")
        val insert_operand = self.symbol_to_operand(insert_symbol)

        # Call set.insert(elem) -> returns bool
        val insert_result = self.builder.emit_call(
            insert_operand,
            [mir_operand_copy(set_local), mir_operand_copy(elem_local)],
            MirType__bool()
        )
        # We ignore the bool result (whether element was new)

    # 3. Return the populated set
    set_local
```

### Step 3: Handle Empty Sets

```simple
# Special case for empty set: s{}
if elements.is_empty():
    # Just call Set.new() and return
    val set_new_symbol = self.resolve_static_method("Set", "new")
    val set_new_operand = self.symbol_to_operand(set_new_symbol)
    return self.builder.emit_call(
        set_new_operand,
        [],
        MirType(kind: MirTypeKind.Named("Set", [MirType__i64()]))
    )
```

---

## Complete Implementation

```simple
me lower_set_lit(elements: [HirExpr]) -> LocalId:
    """Lower set literal to Set.new() + insert() calls.

    Transforms: s{1, 2, 3}
    Into:
        val set = Set.new()
        set.insert(1)
        set.insert(2)
        set.insert(3)
        set
    """
    # Infer element type
    val elem_type = if elements.len() > 0:
        self.infer_expr_type(elements[0])
    else:
        MirType__i64()  # Default for empty sets

    val set_type = MirType(kind: MirTypeKind.Named("Set", [elem_type]))

    # Special case: empty set s{}
    if elements.is_empty():
        val set_new_symbol = self.resolve_static_method("Set", "new")
        val set_new_operand = self.symbol_to_operand(set_new_symbol)
        return self.builder.emit_call(set_new_operand, [], set_type)

    # 1. Generate: val set = Set.new()
    val set_new_symbol = self.resolve_static_method("Set", "new")
    val set_new_operand = self.symbol_to_operand(set_new_symbol)
    val set_local = self.builder.emit_call(set_new_operand, [], set_type)

    # 2. Generate: set.insert(elem) for each element
    for element in elements:
        val elem_local = self.lower_expr(element)

        # Resolve insert method
        val insert_symbol = self.resolve_method(set_type, "insert")
        val insert_operand = self.symbol_to_operand(insert_symbol)

        # Call set.insert(elem) -> bool (ignore result)
        self.builder.emit_call(
            insert_operand,
            [mir_operand_copy(set_local), mir_operand_copy(elem_local)],
            MirType__bool()
        )

    # 3. Return the populated set
    set_local
```

---

## Required Helper Methods

These methods may need to be added to the MIR lowering context:

### 1. `resolve_static_method`

```simple
me resolve_static_method(type_name: text, method_name: text) -> SymbolId:
    """Resolve static method on a type."""
    # Look up "Set" type in symbol table
    # Find static method "new" on that type
    # Return symbol ID
    # If not found, emit error and return dummy symbol
```

### 2. `resolve_method`

```simple
me resolve_method(type: MirType, method_name: text) -> SymbolId:
    """Resolve instance method on a type."""
    # Look up method on the given type
    # Return symbol ID
    # If not found, emit error and return dummy symbol
```

### 3. `infer_expr_type`

```simple
me infer_expr_type(expr: HirExpr) -> MirType:
    """Infer the MIR type of a HIR expression."""
    # Extract type from HIR expression
    # Convert HIR type to MIR type
    # Return MirType
```

---

## Testing Plan

### Unit Tests

1. **Empty set**
   ```simple
   val empty = s{}
   check empty.is_empty()
   ```

2. **Integer set**
   ```simple
   val nums = s{1, 2, 3}
   check nums.len() == 3
   check nums.has(2)
   ```

3. **String set**
   ```simple
   val words = s{"hello", "world"}
   check words.len() == 2
   ```

4. **Duplicate removal**
   ```simple
   val nums = s{1, 2, 2, 3, 3, 3}
   check nums.len() == 3
   ```

5. **Set operations**
   ```simple
   val a = s{1, 2, 3}
   val b = s{2, 3, 4}
   val c = a.union(b)
   check c.len() == 4
   ```

### Integration Tests

Run existing tests in `test/system/collections/set_literal_spec.spl`:
- All 17 tests should pass
- Remove `@skip` comment after implementation complete

---

## Timeline

| Task | Duration | Dependencies |
|------|----------|--------------|
| Add helper methods | 2 hours | None |
| Complete `lower_set_lit()` | 1 hour | Helper methods |
| Unit testing | 1 hour | Implementation |
| Enable integration tests | 30 min | Unit tests pass |
| Documentation | 30 min | All tests pass |
| **Total** | **5 hours** | - |

---

## Dependencies

**Blockers:**
- None (can implement now)

**Nice to have:**
- Type inference improvements for better element type detection
- Optimization: recognize constant sets and pre-compute at compile time

**Enables:**
- 2 skipped tests immediately passable
- Set operations in user code
- More idiomatic collection literals

---

## Risks & Mitigation

**Low Risk:**
- Pattern is well-established (similar to dict/array literals)
- Standard library Set implementation is complete and tested
- Parser already handles the syntax correctly

**Medium Risk:**
- Need to ensure method resolution works correctly
- MIR builder API might not have all needed methods

**Mitigation:**
- Start with simple test case (empty set)
- Incremental implementation and testing
- Use existing array/dict literal lowering as reference

---

## Alternative Approaches

### Option 1: Desugar to Constructor Call

Instead of MIR-level transformation, desugar in HIR:

```simple
# Transform in HIR lowering:
s{1, 2, 3}
# Becomes:
Set.from([1, 2, 3])
```

**Pros:**
- Simpler implementation
- Uses existing `Set.from()` method
- Less MIR code

**Cons:**
- Creates temporary array
- Less efficient (allocates array then set)
- Doesn't match the "literal" semantics

### Option 2: Special Set Aggregate

Add `AggregateKind.Set` to MIR:

```simple
enum AggregateKind:
    Array(elem_type: MirType)
    Tuple
    Struct(def_id: DefId)
    Set(elem_type: MirType)  # NEW
```

**Pros:**
- Treats sets as true literals
- Codegen can optimize construction
- Matches array/tuple pattern

**Cons:**
- More invasive change to MIR
- Codegen needs to handle Set construction
- Doesn't leverage existing Set.new() path

**Recommendation:** Stick with Option 1 (method call lowering) for now, consider Option 2 for optimization later.

---

## Next Steps

1. ✅ Create this implementation plan
2. ⏳ Implement helper methods (`resolve_static_method`, `resolve_method`, `infer_expr_type`)
3. ⏳ Complete `lower_set_lit()` implementation
4. ⏳ Add unit tests for set literal lowering
5. ⏳ Enable integration tests (`test/system/collections/set_literal_spec.spl`)
6. ⏳ Remove `@skip` markers
7. ⏳ Verify all 2 tests pass
8. ⏳ Update feature documentation

---

## Success Criteria

1. ✅ `s{}` syntax creates empty set
2. ✅ `s{1, 2, 3}` creates set with 3 elements
3. ✅ Duplicates are automatically removed
4. ✅ Set operations (union, intersect, etc.) work correctly
5. ✅ All 17 tests in `set_literal_spec.spl` pass
6. ✅ Performance is reasonable (within 2x of manual Set.new() + insert)
7. ✅ Documentation updated
