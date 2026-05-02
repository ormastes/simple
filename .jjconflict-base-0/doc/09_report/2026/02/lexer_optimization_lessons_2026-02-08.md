# Lexer Comprehensive Spec - Optimization Notes

**Date:** 2026-02-08
**File:** test/compiler/lexer_comprehensive_spec.spl

## Initial Attempt - Lessons Learned

### Mistake: Over-Aggressive Constructor Replacement

**What we did wrong:**
Changed all `Lexer.new("source")` to `Lexer("source")`

**Why it failed:**
The Lexer class has a legitimate `static fn new()` method that does important initialization:

```simple
impl Lexer:
    static fn new(source: text) -> Lexer:
        Lexer(
            source: source,
            pos: 0,
            line: 1,
            col: 1,
            # ... more initialization
        )
```

**Result:**
- Direct `Lexer("source")` construction requires all fields
- `Lexer.new()` provides default initialization
- Tests failed with "expected nil to equal true" because lexer was nil

### Key Learning

**Not all `.new()` methods are deprecated!**

✅ **Keep .new() when:**
- It's a `static fn new()` that does initialization
- It sets default values for fields
- It's in the source code, not just test code

❌ **Replace .new() when:**
- It's a simple wrapper with no logic
- Direct construction works fine
- It's only in test code using old patterns

### Correct Approach for lexer_comprehensive_spec

**Only fix the expect syntax:**
```simple
# Before
expect lexer.pos == 0
expect lexer.is_at_end() == true

# After
expect(lexer.pos).to_equal(0)
expect(lexer.is_at_end()).to_equal(true)
```

**Keep Lexer.new() unchanged:**
```simple
# Correct - keep as is
val lexer = Lexer.new("source")
```

## Performance Impact Analysis

### Expected vs Actual

**Expected:**
- Similar to allocator_spec: 5.2s → 0.2s (25x speedup)
- Only syntax overhead, no large loops

**Actual (first attempt):**
- 5.2s → 22.8s (4.4x **slower**!)
- Tests failing early with nil errors
- Only 9 tests running instead of 82

**Why slower:**
- All 82 tests creating lexers that return nil
- Semantic analysis failing on every test
- More error handling overhead

## Correct Optimization Strategy

### Changes to Apply

1. **Expect syntax only** (167 occurrences)
   ```simple
   expect X == Y → expect(X).to_equal(Y)
   ```

2. **No constructor changes** (0 occurrences)
   ```simple
   Keep: Lexer.new("source")
   ```

3. **Remove @skip** (1 occurrence)

### Expected Improvement

**Conservative estimate:**
- Old expect syntax overhead: ~2-3s
- Expected: 5.2s → 2-3s (2x speedup)

**Why not as dramatic:**
- No large loops to reduce
- No .new() overhead to remove
- Only syntax parsing improvement

## Comparison with Other Optimizations

| Test | Original | Expected | Actual | Main Optimization |
|------|----------|----------|--------|-------------------|
| literal_converter | 16.0s | 3.6s | 1.7s | Data reduction + methods |
| allocator | 9.1s | 0.2s | 0.2s | Syntax + loops + constructors |
| lexer | 5.2s | 2-3s | TBD | **Syntax only** |

## Updated Optimization Checklist

Before replacing `.new()`, check:
- [ ] Is it a `static fn new()` in source code?
- [ ] Does it do initialization logic?
- [ ] Does it set default values?
- [ ] Is direct construction possible with all fields?

If ANY are true → **KEEP .new()**

## Next Steps

1. ✅ Revert constructor changes
2. 🔄 Keep only expect syntax fixes (in progress)
3. ⏳ Test and measure actual improvement
4. 📝 Update optimization guide with this learning

---

**Key Takeaway:** Not all patterns are universal. Always verify the actual implementation before making assumptions.
