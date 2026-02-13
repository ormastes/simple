# Newly Discovered Refactoring Opportunity

**Date**: 2026-02-13 01:48 UTC  
**Discovery**: Final deep scan of 10+ line duplications

## Pattern: ASCII Character Code Conversion

### Summary
Found 7 files reimplementing `char_from_code()` function, which already exists and is exported from `std/string.spl`.

### Files Affected:
1. ✅ `std/string.spl` - **char_from_code()** - CANONICAL (keep)
2. ❌ `std/serialization_utils.spl` - **char_from_code_safe()** - duplicate
3. ❌ `std/base_encoding_utils.spl` - **char_from_code()** - duplicate
4. ❌ `std/avro/utilities.spl` - **avro_code_to_char()** - duplicate
5. ❌ `std/base64/utilities.spl` - **char_from_code()** - duplicate
6. ❌ `std/smtp/utilities.spl` - **text_from_char_code()** - duplicate
7. ❌ `std/buffer/utilities.spl` - **code_to_char()** - duplicate

### Duplicated Code Pattern (10+ lines):
```simple
if code == 48: return "0"
if code == 49: return "1"
if code == 50: return "2"
if code == 51: return "3"
if code == 52: return "4"
if code == 53: return "5"
if code == 54: return "6"
if code == 55: return "7"
if code == 56: return "8"
if code == 57: return "9"
# ... continues for A-Z, a-z
```

Each implementation is ~80 lines of identical if-statement chains converting ASCII codes to characters.

## Refactoring Plan

### Step 1: Verify Canonical Implementation
The canonical implementation in `std/string.spl` is complete and exported:
```simple
fn char_from_code(code: i64) -> text:
    # Handles all ASCII: 0-9, A-Z, a-z, special chars
    ...

export char_from_code
```

### Step 2: Refactor Each File

For each duplicate file:

1. Add import: `use string.{char_from_code}`
2. Replace local implementation with import
3. Update all call sites to use `char_from_code`
4. Test build

Example for `base_encoding_utils.spl`:

**Before:**
```simple
fn char_from_code(code: i64) -> text:
    if code == 48: return "0"
    ... [80 lines]
    ""
```

**After:**
```simple
use string.{char_from_code}
```

### Step 3: Handle Name Variations

Some files use different names. Need to either:
- Option A: Create alias: `fn char_from_code_safe(code: i64) -> text: char_from_code(code)`
- Option B: Update all call sites to use `char_from_code` directly

## Impact Assessment

### Lines Saved:
- 7 files × ~80 lines each = **~560 lines**
- Plus removes maintenance burden of 7 duplicate implementations

### Effort Required:
- **Time**: 1-2 hours
- **Risk**: Low (simple import + replace)
- **Testing**: Verify each file's build after change

### Benefits:
1. **Single Source of Truth**: Only string.spl has the implementation
2. **Consistency**: All files use same function
3. **Maintainability**: Changes only needed in one place
4. **Performance**: No change (same code)

## Recommendation

✅ **RECOMMENDED** for next refactoring session

This is a straightforward refactoring with high impact:
- Clear pattern
- Canonical implementation exists
- Already exported
- Just need imports and replacements

## Status

- **Discovered**: 2026-02-13 01:48 UTC
- **Status**: Not yet refactored
- **Priority**: Medium (good follow-up to current session)
- **Blocked**: No blockers, ready to implement

## Updated Session Totals

If this is refactored:
- Current: 170 duplications eliminated
- With char_from_code: **177 duplications** (52% of 340)
- Additional savings: **~560 lines**

---

**Note**: This was discovered after the main refactoring session was marked complete. Consider for follow-up work or separate PR.
