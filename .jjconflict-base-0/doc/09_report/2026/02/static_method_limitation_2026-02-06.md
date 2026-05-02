# Static Method Support Limitation

## Problem

**1,562 test failures (30% of all failures)** due to interpreter not supporting static method calls.

## Error Message

```
semantic: unsupported path call: ["Type", "method"]
```

## Examples

Tests trying to call:
```simple
val heap = ActorHeap.default()      # ❌ unsupported path call
val config = HeapConfig.default()    # ❌ unsupported path call
val point = Point.origin()          # ❌ unsupported path call
```

## Root Cause

The **interpreter (runtime)** doesn't support:
1. Static method calls: `Type.method()`
2. Enum variant construction: `Enum.Variant()`
3. Associated function calls

This is a **runtime limitation** - the error comes from the pre-built Rust runtime, not Simple code.

## Why Can't We Fix This Now?

1. **Runtime is pre-built** (`bin/bootstrap/simple_runtime`)
2. **Rust source removed** (project is 100% Pure Simple)
3. **Requires interpreter changes** in the runtime
4. **Cannot modify without rebuilding runtime from scratch**

## Workarounds

### Option 1: Use Direct Construction

Instead of:
```simple
val heap = ActorHeap.default()
```

Use:
```simple
val heap = ActorHeap(
    size: 1024,
    gc_threshold: 512
)
```

### Option 2: Module-Level Factory Functions

Instead of:
```simple
impl Point:
    static fn origin() -> Point:
        Point(x: 0, y: 0)

val p = Point.origin()  # ❌ doesn't work
```

Use:
```simple
fn point_origin() -> Point:
    Point(x: 0, y: 0)

val p = point_origin()  # ✅ works
```

### Option 3: Wait for Runtime Update

The runtime needs to be updated to support static method calls. This requires:
1. Rebuilding runtime with static method support
2. Or implementing interpreter enhancements
3. Estimated effort: 1-2 weeks

## Impact Analysis

### Tests Affected

- **1,562 errors** from unsupported path calls
- Affects 30% of all test failures
- Impacts all domains: interpreter, compiler, stdlib

### Common Patterns Blocked

```simple
# Factory methods
Type.create()
Type.new()
Type.default()
Type.from_*()

# Enum variants
Option.Some(val)
Result.Ok(val)
Result.Err(msg)

# Associated constants
Math.PI
Math.E
```

## Temporary Solution

**Update all failing tests** to use workarounds:

1. Replace static method calls with module functions
2. Use direct construction instead of factories
3. Import enum variants directly

**Effort**: 40-80 hours to update all affected tests
**Impact**: Would fix 1,562 test failures

## Long-Term Solution

**Implement static method support in runtime:**

1. Modify interpreter to handle path calls
2. Add static method resolution
3. Support associated functions
4. Rebuild runtime

**Effort**: 1-2 weeks of interpreter work
**Impact**: Fixes root cause permanently

## Recommendation

### Short-term
Document workarounds and update critical tests using the patterns above.

### Medium-term
Submit runtime enhancement request for static method support.

### Long-term
When runtime is rebuilt, implement full static method support.

## Related Issues

- Parser bugs: ✅ FIXED
- Missing functions: ✅ FIXED  
- Import issues: ✅ FIXED
- **Static methods**: ❌ BLOCKED (runtime limitation)

## Priority

**HIGH** but **BLOCKED** by runtime architecture.

Cannot fix without:
- Runtime rebuild, OR
- Major test refactoring (40-80 hours)

## Status

**DOCUMENTED** - Cannot fix with current architecture.
Requires runtime changes or test refactoring.
