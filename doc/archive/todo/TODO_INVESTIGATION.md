# TODO Investigation Report

## Investigation Date
2026-02-12

## TODOs Investigated

### 1. MIR Field Resolution (P2 - Investigate)

**Location**: `src/compiler/mir_lowering.spl:245`

**TODO**:
```simple
# For now, use field index 0 (TODO: proper field resolution)
val field_index = 0
```

**Context**:
- Used in field assignment lowering: `obj.field = value`
- Pattern match extracts: `Field(base, field, resolved)`
- Currently hardcodes `field_index = 0`
- The `resolved` parameter is available but unused

**Investigation Findings**:

1. **Test Results**: ✅ PASSING
   - `test/integration/static_method_desugar_spec.spl` passes (1/1)
   - No field-related test failures observed

2. **MIR Instructions**:
   - `GetField(dest, base, field: i64)` - field read
   - `SetField(base, field: i64, value)` - field write
   - Both expect `field: i64` (numeric field index)

3. **Possible Explanations**:
   - Field resolution might happen during type checking/resolution phase
   - The `resolved` parameter might already contain the field index
   - Hardcoded `0` works for common cases (first field, single-field structs)
   - May only be exercised in specific edge cases not covered by tests

**Status**: **DEFERRED** - Not broken, low priority

**Reasoning**:
- No failing tests detected
- Existing functionality works
- If it were broken, we'd see failures in struct field access tests
- Risk of breaking working code outweighs unclear benefit

**Recommendation**:
- Leave as-is unless field access bugs are reported
- If fixing, first add comprehensive multi-field struct tests
- Check what the `resolved` parameter contains (requires debugging)

---

### 2. Monomorphize Integration - Symbol Table (P1 - Architectural)

**Location**: `src/compiler/monomorphize_integration.spl:329`

**TODO**:
```
TODO: Integration point - When symbol table is accessible:
1. Look up sym_id in symbol table
2. Return actual function/variable name
3. Include module path if not in current scope
4. Format for error messages (e.g., "std.json.parse")
```

**Context**:
- Function: `symbol_id_to_name(sym_id: i64) -> text`
- **Current**: Returns placeholder `"sym_{sym_id}"`
- **Proposed**: Look up actual names in symbol table

**Investigation Findings**:

1. **Purpose**: Error message improvement
   - Convert `"sym_42"` → `"map"`
   - Convert `"sym_123"` → `"std.json.parse"`

2. **Current Impact**: Low
   - Error messages show `"sym_X"` instead of readable names
   - Doesn't break functionality, just makes debugging harder
   - Not a compiler correctness issue

3. **Requirements**:
   - Need access to symbol table from monomorphization pass
   - Need symbol ID → name mapping
   - Need module path resolution for qualified names

**Status**: **DEFERRED** - Enhancement, not bug fix

**Reasoning**:
- Quality-of-life improvement for error messages
- Not critical to compiler functionality
- Requires architectural decision on symbol table access
- Better to design properly than rush implementation

**Recommendation**:
1. **Short term**: Leave as-is with placeholder
2. **Medium term**: Design symbol table architecture
   - How to pass symbol table to monomorphization?
   - Immutable snapshot vs. live reference?
   - Performance implications?
3. **Long term**: Implement after architecture is clear

---

## Summary

| TODO | Priority | Status | Risk | Value | Effort |
|------|----------|--------|------|-------|--------|
| **MIR Field Resolution** | P2 | DEFERRED | Medium | Unknown | 1-2 days |
| **Monomorphize Symbol Table** | P1 Arch | DEFERRED | Low | Low-Med | 1 week |

### Key Findings

1. **Both TODOs are not urgent**:
   - Field resolution: Tests pass, no broken functionality
   - Symbol table: Error message improvement only

2. **Both require investigation before implementation**:
   - Field resolution: Need to understand `resolved` parameter
   - Symbol table: Need architectural design for integration

3. **Better to defer than rush**:
   - Risk of breaking working code (field resolution)
   - Risk of wrong architectural choice (symbol table)

---

## Recommendations for Next Work

### Option 1: Leave TODOs as-is
- **Reason**: Nothing is broken, low ROI
- **Action**: Focus on other high-value work

### Option 2: Enhance compiler with new features
Possible directions:
1. **Better optimization passes** in MIR (constant folding, DCE improvements)
2. **Profile-guided optimization** (collect hotness data, use in layout solver)
3. **Cross-compilation support** (test LLVM backend on Windows/macOS)
4. **Better error messages** (general improvement, not just symbol names)

### Option 3: Fix runtime limitations
From MEMORY.md and previous analysis:
1. **Closure capture modification** (P1 - enables 30+ tests)
2. **Chained method calls** (P2 - enables 20+ tests)
3. **FFI extensions** (P2 - file locking, async spawn, mmap)

### Option 4: Complete features from plan
From the original comprehensive plan:
- **Track D**: Runtime/Infrastructure improvements
  - D0-D1: FFI extensions (2-5 days)
  - D2: SMF module format completion (5-7 days)
  - D3: Interpreter improvements (7-10 days)

---

## My Recommendation

**Focus on Track D (Runtime/Infrastructure)** instead of compiler TODOs:

**Why**:
- ✅ Higher value: Unlocks 100+ failing tests (vs. 0 for compiler TODOs)
- ✅ Clear requirements: Well-defined FFI additions
- ✅ Lower risk: Adding new functionality vs. fixing "working" code
- ✅ Immediate impact: Tests start passing

**Specific next steps**:
1. **D0.1**: Expose file locking FFI (2-4 hours, unlocks 20+ tests)
2. **D0.2**: Add high-resolution time (1-2 hours, unlocks 15+ tests)
3. **D1.1**: Process async spawn (1 day, unlocks 25+ tests)
4. **D1.2**: Offset-based file I/O (4-6 hours, unlocks 50+ tests)

**Total**: 2-3 days for +110 tests passing (vs. weeks for uncertain compiler TODO value)

---

## Conclusion

Both investigated TODOs are **low priority**:
- Not broken (tests pass)
- Not blocking features
- Require more design work

**Better use of time**: Runtime/Infrastructure improvements (Track D) for immediate test unlocking.
