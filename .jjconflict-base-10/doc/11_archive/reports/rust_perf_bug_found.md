# Rust Performance Bug: Unnecessary Expression Tree Cloning

**Date:** 2026-01-31
**Severity:** HIGH
**Impact:** O(n) deep copy on every expression lowering (potentially O(n²) for nested expressions)

## Bug Description

**File:** `rust/compiler/src/mir/lower/lowering_expr.rs`
**Location:** Line 15 in `lower_expr()` method

The MIR lowering pass clones the entire expression tree for every expression it processes:

```rust
pub(super) fn lower_expr(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
    let expr_ty = expr.ty;
    let expr_kind = expr.kind.clone();  // ❌ DEEP COPY OF ENTIRE EXPRESSION TREE!

    match &expr_kind {
        // ... pattern matching
    }
}
```

## Why This Is a Problem

### HirExprKind Contains Recursive Structures

```rust
pub enum HirExprKind {
    Binary {
        op: BinOp,
        left: Box<HirExpr>,     // Deep clone!
        right: Box<HirExpr>,    // Deep clone!
    },
    Call {
        func: Box<HirExpr>,     // Deep clone!
        args: Vec<HirExpr>,     // Clones all arguments!
    },
    MethodCall {
        receiver: Box<HirExpr>, // Deep clone!
        args: Vec<HirExpr>,     // Clones all arguments!
        // ...
    },
    Array(Vec<HirExpr>),        // Clones entire array!
    Dict(Vec<(HirExpr, HirExpr)>), // Clones all keys and values!
    // ... many more recursive cases
}
```

### Performance Impact

For an expression like `(a + b) * (c + d) * (e + f)`:

1. **First call** to `lower_expr` on root multiplication:
   - Clones entire expression tree (9 nodes)

2. **Recursive calls** on sub-expressions:
   - Left multiply: clones `(a + b) * (c + d)` (5 nodes)
   - Right multiply: clones `(e + f)` (3 nodes)
   - Each addition: clones 3 nodes each

**Total clones:** ~30+ nodes for a simple 9-node expression tree

For deeply nested expressions (e.g., chained method calls, nested arrays), this becomes **O(n²)** or worse.

## Expected Performance Impact

**Current (with bug):**
- Simple expression (10 nodes): ~30 clones
- Complex expression (100 nodes): ~500-1000 clones
- Deeply nested (1000 nodes): ~10,000+ clones

**After fix (pattern match by reference):**
- Any expression: 0 clones
- **Expected speedup:** 10-100x for expression-heavy code

## The Fix

### Option 1: Pattern Match by Reference (Recommended)

```rust
pub(super) fn lower_expr(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
    let expr_ty = expr.ty;
    // ✅ No clone - pattern match on reference
    match &expr.kind {
        HirExprKind::Integer(n) => {
            let n = *n;  // Only copy the i64, not the tree
            // ...
        }
        HirExprKind::String(s) => {
            // Clone only the string when needed
            self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ConstString {
                    dest,
                    value: s.clone()  // Only clone the string value
                });
                dest
            })
        }
        // ... other cases
    }
}
```

### Option 2: Arc/Rc Wrapping (If Sharing Needed)

If expression trees need to be shared across multiple lowering contexts:

```rust
pub struct HirExpr {
    pub kind: Arc<HirExprKind>,  // Cheap to clone (just ref count)
    pub ty: TypeId,
}
```

**Trade-off:** Adds indirection and reference counting overhead, but makes cloning O(1).

## Why Current Code Uses Clone

Looking at the match statement, most branches don't actually need the clone - they just extract specific fields:

```rust
match &expr_kind {
    HirExprKind::Integer(n) => {
        let n = *n;  // Only needs the i64, not the whole tree
        // ...
    }
    HirExprKind::String(s) => {
        let s = s.clone();  // Only needs the String, not the tree
        // ...
    }
}
```

The clone at line 15 is unnecessary - each branch can clone only what it needs.

## Verification

To verify the fix doesn't break anything:

1. Run existing compiler tests:
   ```bash
   cd rust && cargo test --package simple-compiler
   ```

2. Run MIR lowering tests specifically:
   ```bash
   cd rust && cargo test --package simple-compiler lower_expr
   ```

3. Benchmark compilation time on large files:
   ```bash
   # Before fix:
   time ./rust/target/release/simple_runtime compile large_file.spl

   # After fix:
   time ./rust/target/release/simple_runtime compile large_file.spl
   ```

## Estimated Impact

For the Simple compiler on typical codebases:

| Code Size | Current | After Fix | Speedup |
|-----------|---------|-----------|---------|
| Small (100 exprs) | 50ms | 5ms | 10x |
| Medium (1000 exprs) | 800ms | 40ms | 20x |
| Large (10000 exprs) | 15s | 400ms | 37x |

**Note:** These are estimates based on the assumption that expression lowering is a significant portion of compilation time. Actual impact depends on the overall compiler pipeline.

## Related Issues

This pattern might exist in other lowering passes:

**Files to check:**
- `rust/compiler/src/mir/lower/lowering_stmt.rs` - Statement lowering
- `rust/compiler/src/mir/lower/lowering_core.rs` - Core lowering
- `rust/compiler/src/hir/lower/*.rs` - HIR lowering passes

**Search for similar patterns:**
```bash
grep -n "\.kind\.clone()" rust/compiler/src/*/lower/*.rs
grep -n "\.clone().*match" rust/compiler/src/*/lower/*.rs
```

## Next Steps

1. ✅ Document the bug (this file)
2. ⏳ Fix `lowering_expr.rs` by removing the clone
3. ⏳ Search for similar patterns in other lowering passes
4. ⏳ Run tests to verify no regressions
5. ⏳ Benchmark to measure actual performance improvement
6. ⏳ Consider if other AST/HIR/MIR types have similar issues

## Additional Notes

This bug highlights a common Rust pitfall: **unnecessary cloning to satisfy the borrow checker**. The developer likely added `.clone()` to avoid borrowing issues, but pattern matching by reference (`&expr.kind`) achieves the same goal without the performance cost.

**Best Practice:** When processing tree structures:
- ❌ Don't clone the entire tree
- ✅ Pattern match by reference
- ✅ Clone only specific fields when needed
- ✅ Use `Arc<T>` if sharing is required
