# Primitive API Migration - Future Opportunities
**Date**: 2026-01-20
**Status**: Infrastructure Complete - Optional Enhancements
**Prerequisites**: Read `newtype_design_patterns.md` and `../report/primitive_api_migration_complete_2026-01-20.md`

---

## Purpose

This document outlines the remaining 52 "potential opportunity" warnings from the primitive API migration project. These are optional enhancements that could be addressed incrementally as refactoring opportunities arise.

**Important**: The infrastructure is production-ready. These are **optional improvements**, not blockers.

---

## Summary of Remaining Work

| Category | Count | Effort | Value | Priority |
|----------|-------|--------|-------|----------|
| UI Widget Dimensions | ~12 | Medium | Low | Optional |
| LMS Session Timestamps | 3 | High | Medium | Future |
| File I/O Return Types | 6 | Medium | Medium | Optional |
| TUI Event Codes | 8 | Low | Low | Optional |
| SeekFrom Offsets | 3 | Low | Low | Keep as-is |
| Misc. Counts/Indices | ~20 | Varies | Varies | Case-by-case |

**Total**: ~52 warnings

---

## Category 1: UI Widget Dimensions (12 warnings)

### Current State
```simple
# simple/std_lib/src/ui/widget.spl (estimated, struct not fully visible)

pub struct Padding:
    top: i32        # Warning
    right: i32      # Warning
    bottom: i32     # Warning
    left: i32       # Warning

pub struct BoxConstraints:
    min_width: i32      # Warning
    max_width: i32      # Warning
    min_height: i32     # Warning
    max_height: i32     # Warning
```

### Proposed Solution
```simple
# simple/std_lib/src/units/ui.spl (new file)

unit PixelDimension: i32 as px_dim

impl PixelDimension:
    pub fn from_i32(n: i32) -> PixelDimension:
        return n_px_dim

    pub fn value() -> i32:
        return self as i32

    pub fn zero() -> PixelDimension:
        return 0_px_dim

    pub fn is_negative() -> bool:
        """Check if dimension is negative (invalid for sizes)."""
        return self.value() < 0

# Update structs
pub struct Padding:
    top: PixelDimension
    right: PixelDimension
    bottom: PixelDimension
    left: PixelDimension
```

### Analysis
**Pros**:
- Prevents confusion between pixel dimensions and other i32 values
- Helper methods like `is_negative()` add validation

**Cons**:
- UI coordinates are inherently primitive (x, y positions)
- No real semantic distinction between top/right/bottom/left
- Just wrapping i32 doesn't add much value

**Recommendation**: **Low priority - optional**. Only worth doing if adding domain operations like `clamp_to_screen()` or validation.

**Effort**: ~2 hours (create type, update widget.spl, test)

---

## Category 2: LMS Session Timestamps (3 warnings)

### Current State
```simple
# simple/std_lib/src/lms/session.spl

pub class Session:
    created_at: i32          # Unix timestamp in milliseconds
    last_activity: i32       # Unix timestamp in milliseconds

    pub fn get_age() -> i32:        # Warning
        val now = sys.time.now_ms()
        return now - self.created_at

    pub fn get_idle_time() -> i32:  # Warning
        val now = sys.time.now_ms()
        return now - self.last_activity

    pub fn is_idle(threshold_ms: i32) -> bool:  # Warning
        return self.get_idle_time() > threshold_ms
```

### Proposed Solution
```simple
# Requires broader refactoring

pub class Session:
    created_at: Milliseconds     # Change from i32 to u64
    last_activity: Milliseconds  # Change from i32 to u64

    pub fn get_age() -> Milliseconds:
        val now = sys.time.now_ms_typed()  # New function returning Milliseconds
        return now.sub(self.created_at)

    pub fn get_idle_time() -> Milliseconds:
        val now = sys.time.now_ms_typed()
        return now.sub(self.last_activity)

    pub fn is_idle(threshold: Milliseconds) -> bool:
        return self.get_idle_time().exceeds(threshold)
```

### Analysis
**Pros**:
- Type-safe duration arithmetic
- Cannot confuse milliseconds with other integer values
- Helper methods like `exceeds()` improve readability

**Cons**:
- Requires changing i32 → u64 (breaking change to Session struct)
- Requires adding `sys.time.now_ms_typed()` or similar
- Affects serialization/deserialization of Session
- Moderate refactoring effort

**Recommendation**: **Future work - moderate priority**. Worth doing during next LMS refactoring, but not urgent.

**Effort**: ~4-6 hours (change Session fields, update all call sites, update sys.time API, test)

---

## Category 3: File I/O Return Types (6 warnings)

### Current State
```simple
# simple/std_lib/src/host/sync_nogc_mut/io/fs/ops.spl

pub fn write_text(path: FilePath, text: str) -> i32:  # Warning
    # Returns: bytes written (positive) or error code (negative)

pub fn append_text(path: FilePath, text: str) -> i32:  # Warning
    # Returns: bytes written (positive) or error code (negative)
```

### Proposed Solution Option A: Result Type
```simple
pub fn write_text(path: FilePath, text: str) -> Result<ByteCount, IoError>:
    # Clear success/error distinction
```

**Pros**:
- Idiomatic error handling
- Type-safe byte counts

**Cons**:
- Breaking API change
- Existing code expects i32 return

**Effort**: ~3-4 hours

### Proposed Solution Option B: Wrapper Type
```simple
unit WriteResult: i32 as write_res

impl WriteResult:
    pub fn from_i32(n: i32) -> WriteResult:
        return n_write_res

    pub fn is_error() -> bool:
        return self.value() < 0

    pub fn bytes_written() -> Option<ByteCount>:
        val n = self.value()
        if n < 0:
            return None
        return Some((n as u64)_bytes)

    pub fn error_code() -> Option<i32>:
        val n = self.value()
        if n < 0:
            return Some(n)
        return None
```

**Pros**:
- Non-breaking (still returns integer-like type)
- Adds helper methods for ergonomics

**Cons**:
- Still mixes success/error in one type (not ideal)
- Wrapper doesn't fully solve problem

**Effort**: ~2 hours

### Analysis
**Recommendation**: **Option A (Result type) - moderate priority**. Worth doing next time sync_nogc_mut I/O is refactored. Option B is a half-measure.

**Effort**: Option A = ~3-4 hours, Option B = ~2 hours

---

## Category 4: TUI Event Codes (8 warnings)

### Current State
```simple
# simple/std_lib/src/ui/tui/backend/ratatui.spl

pub struct RawEvent:
    event_type: u32     # Warning
    key_code: u32       # Warning
    key_mods: u32       # Warning
    char_value: u32     # Warning

# simple/std_lib/src/ui/common/key_codes.spl

pub enum KeyCode:
    F(u8)               # Warning - F-key number
    # ...

pub struct KeyModifiers:
    shift: bool         # Warning (predicate, actually OK)
    ctrl: bool          # Warning (predicate, actually OK)
    alt: bool           # Warning (predicate, actually OK)
```

### Analysis
**RawEvent fields**: These are FFI boundary values from underlying TUI library (likely ratatui/crossterm). Wrapping u32 codes adds no value since they're opaque library constants.

**KeyCode::F(u8)**: F-key numbers (F1=1, F2=2, ..., F12=12). Could create `FKeyNumber` unit type, but u8 is clear and standard.

**KeyModifiers bools**: These are predicates (is shift pressed?). Warnings are false positives - bools are appropriate.

**Recommendation**: **Keep as-is**. These are appropriate primitive uses.

**Effort**: N/A (no work needed)

---

## Category 5: SeekFrom Offsets (3 warnings)

### Current State
```simple
# simple/std_lib/src/host/common/io/types.spl

pub enum SeekFrom:
    Start(u64)      # Warning - absolute position from start
    End(i64)        # Warning - signed offset from end
    Current(i64)    # Warning - signed offset from current

# Example usage:
file.seek(SeekFrom::Start(1024))      # Seek to byte 1024
file.seek(SeekFrom::End(-100))        # 100 bytes before EOF
file.seek(SeekFrom::Current(50))      # 50 bytes forward
```

### Analysis
**Why different types?**:
- `Start(u64)`: Absolute position, always non-negative
- `End(i64)` / `Current(i64)`: Relative offsets, can be negative

**Could we wrap?**:
```simple
unit AbsolutePosition: u64 as abs_pos
unit RelativeOffset: i64 as rel_offset

pub enum SeekFrom:
    Start(AbsolutePosition)
    End(RelativeOffset)
    Current(RelativeOffset)
```

**Pros**: Semantic distinction between absolute/relative

**Cons**:
- Matches Rust std::io::SeekFrom (industry standard)
- Unsigned/signed already provides semantic meaning
- Wrapping adds no value

**Recommendation**: **Keep as-is**. This is a well-designed API following industry standards (POSIX lseek, Rust std::io).

**Effort**: N/A (no work needed)

---

## Category 6: Miscellaneous Counts/Indices (~20 warnings)

Various warnings across the codebase for counts, indices, and sizes. Examples:

### stdio Write Operations
```simple
# simple/std_lib/src/host/async_nogc_mut/io/stdio.spl

pub fn read(n: i32) -> text:       # Warning - could use Count
pub fn write(text: str) -> i32:    # Warning - could use ByteCount
```

**Analysis**: These are low-level stdio wrappers. Similar to file I/O Category 3 - could use Result<ByteCount> but requires broader refactoring.

**Recommendation**: Address during next stdio module refactor.

### exists() Predicate
```simple
pub fn exists(path: FilePath) -> bool:  # Warning
```

**Analysis**: This is a predicate. Warning is false positive - bool is appropriate.

**Recommendation**: Keep as-is.

### Color RGBA Field
```simple
# simple/std_lib/src/ui/widget.spl

pub struct Color:
    rgba: u32  # Warning - packed RGBA value
```

**Analysis**: This is a packed 32-bit color (0xRRGGBBAA). Could create `PackedColor` or `RGBAValue` type, but u32 is industry standard for packed colors.

**Recommendation**: Keep as-is unless adding color manipulation methods.

---

## Implementation Priority Guide

### High Priority (Address Next)
None - infrastructure is complete.

### Medium Priority (Next Refactoring Cycle)
1. **LMS Session Timestamps** (4-6 hours)
   - Wait for next LMS module refactoring
   - Convert i32 → Milliseconds
   - Update sys.time API

2. **File I/O Result Types** (3-4 hours)
   - Convert i32 → Result<ByteCount, IoError>
   - Update all call sites
   - Test error handling

### Low Priority (Optional Enhancements)
1. **UI Widget Dimensions** (2 hours)
   - Only if adding validation/domain operations
   - Create units/ui.spl with PixelDimension
   - Update widget.spl

### Keep As-Is (Appropriate Primitives)
1. **SeekFrom offsets** - matches industry standards ✓
2. **TUI event codes** - FFI boundary, opaque values ✓
3. **KeyModifiers bools** - predicates, appropriate ✓
4. **exists() predicate** - boolean return appropriate ✓
5. **Color RGBA** - industry standard packed format ✓

---

## Decision Framework for Future Work

Before addressing a warning, ask:

1. **Does wrapping prevent real bugs?**
   - Yes → High priority
   - No → Low priority

2. **Do helper methods add domain value?**
   - Yes → Worth considering
   - No → Keep as primitive

3. **Is this a specification requirement or industry standard?**
   - Yes → Keep as primitive
   - No → Can consider wrapping

4. **Is this a predicate or FFI boundary?**
   - Yes → Keep as primitive
   - No → Can consider wrapping

5. **Does this require breaking changes?**
   - Yes → Defer to next major refactor
   - No → Can address incrementally

---

## Effort Estimates Summary

| Task | Effort | Value | Priority |
|------|--------|-------|----------|
| LMS Session Milliseconds | 4-6 hrs | Medium | Medium |
| File I/O Result Types | 3-4 hrs | Medium | Medium |
| UI Widget Dimensions | 2 hrs | Low | Low |
| SeekFrom Wrappers | N/A | None | Keep as-is |
| TUI Event Codes | N/A | None | Keep as-is |

**Total estimated effort for all optional work**: ~9-12 hours

**Recommendation**: Address incrementally during natural refactoring cycles, not as dedicated work items.

---

## Linter Configuration Recommendations

To suppress false-positive warnings for intentional primitive uses:

```simple
# simple/std_lib/src/host/common/io/types.spl

#[allow(primitive_api)]  // Matches Rust std::io::SeekFrom
pub enum SeekFrom:
    Start(u64)      # Unsigned: absolute position
    End(i64)        # Signed: can be negative offset
    Current(i64)    # Signed: can be negative offset

# simple/std_lib/src/compiler_core/json.spl

#[allow(primitive_api)]  // JSON specification requires primitives
pub enum JsonValue:
    bool(bool)
    Number(f64)
    Integer(i64)
```

**Note**: Linter attribute syntax (`#[allow(...)]`) may need to be implemented in Simple compiler.

---

## Conclusion

The primitive API migration infrastructure is **complete and production-ready**. The remaining 52 warnings fall into three categories:

1. **Appropriate primitives** (~20 warnings) - should stay as-is
2. **Optional enhancements** (~20 warnings) - low value, address opportunistically
3. **Future refactoring targets** (~12 warnings) - medium value, address during natural refactors

**No urgent work remaining**. Future improvements should be driven by actual refactoring needs, not warning elimination.

---

**Document Version**: 1.0
**Last Updated**: 2026-01-20
**Status**: Complete - Optional Future Enhancements Documented
