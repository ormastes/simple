# Performance Optimization: must_use_scan_source() - 2026-02-15

## Problem

The `must_use_scan_source()` function in `src/core/interpreter/eval.spl` (lines 309-397) had a critical O(n⁴) performance issue due to repeated string concatenation in nested loops.

## Original Code Issues

### Issue 1: Line Splitting (O(n²))
```simple
var current_line: text = ""
for _unused in source:              # O(n)
    current_line = current_line + ch # O(n) string concat
```
- Each `+` operator creates a new string by copying all existing characters
- For a file with n characters, this results in O(n²) total character copies

### Issue 2: Line Trimming (O(n³))
```simple
var trimmed: text = ""
for line in lines:                  # O(n) lines
    for _c in line:                 # O(n) chars per line
        trimmed = trimmed + lc      # O(n) string concat
```
- Nested loop over all characters in all lines = O(n²)
- String concatenation inside nested loop = O(n³) total

### Issue 3: Reason Extraction (O(n⁴))
```simple
var reason_buf: text = ""
for line in lines:                  # O(n)
    for _rc in trimmed:             # O(n)
        for each char:              # O(n)
            reason_buf = reason_buf + rc2 # O(n) concat
```
- Triple nested loops with string concatenation = O(n⁴)

### Issue 4: Function Name Extraction (O(n⁴))
```simple
var fname: text = ""
for line in lines:                  # O(n)
    for _fc in trimmed:             # O(n)
        for each char:              # O(n)
            fname = fname + fc2     # O(n) concat
```
- Same O(n⁴) issue as reason extraction

## Solution: Array Push + Join Pattern

Replaced all string concatenation with array building using `.push()` followed by `.join("")`:

### Fixed Line Splitting (O(n))
```simple
var line_chars: [text] = []
for _unused in source:              # O(n)
    line_chars.push(ch)             # O(1) array append
val line = line_chars.join("")      # O(n) to join at end
```
- `.push()` mutates array in place - O(1) per operation
- `.join("")` creates final string once - O(n) total
- Total: O(n) + O(n) = O(n)

### Fixed Line Trimming (O(n))
```simple
var trimmed_chars: [text] = []
for _c in line:                     # O(n)
    trimmed_chars.push(lc)          # O(1)
val trimmed = trimmed_chars.join("")  # O(n)
```

### Fixed Reason Extraction (O(n))
```simple
var reason_chars: [text] = []
for _rc in trimmed:                 # O(n)
    reason_chars.push(rc2)          # O(1)
pending_reason = reason_chars.join("")  # O(n)
```

### Fixed Function Name Extraction (O(n))
```simple
var fname_chars: [text] = []
for _fc in trimmed:                 # O(n)
    fname_chars.push(fc2)           # O(1)
val fname = fname_chars.join("")    # O(n)
```

## Key Implementation Detail

The `.push()` method in the Simple runtime **mutates the array in place** (it does NOT return a new array). This is critical for O(1) performance:

```simple
# CORRECT - mutates in place (O(1))
line_chars.push(ch)

# WRONG - would create copy (O(n))
line_chars = line_chars.push(ch)
```

## Performance Impact

**Before:** O(n⁴) - catastrophic for large files
**After:** O(n) - linear scaling

For a 10,000 character file:
- Before: ~10¹⁶ operations (essentially hangs)
- After: ~10,000 operations (milliseconds)

## Verification

All tests pass with zero regressions:
- `test/unit/core/must_use_spec.spl` - 1/1 passing (5ms)
- `test/unit/core/interpreter/` - 8/8 passing (34ms)
- `test/unit/core/` - 77/77 passing (370ms)
- `test/unit/compiler/` - 227/227 passing (956ms)

## Files Modified

- `src/core/interpreter/eval.spl` - Lines 309-399 optimized
- Total changes: 4 string variables → array variables, 4 concat loops → push loops

## Related Documentation

- Simple Language Runtime Limitations: `MEMORY.md`
- String Performance Best Practices: `doc/guide/syntax_quick_reference.md`
