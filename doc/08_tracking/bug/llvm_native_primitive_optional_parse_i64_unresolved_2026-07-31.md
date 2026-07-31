# LLVM native optional `parse_i64` is unresolved on RV64

- **Filed:** 2026-07-31
- **Status:** OPEN — compiler/runtime root fix required; the eight RV64 entry-live
  call sites validate with `std.convert.is_i64_text` and then use the existing
  full-width `safe_parse_int` until the optional primitive is linkable.

## Failure

The LLVM RV64 native link retains `str.parse_i64` from the canonical
WM/web Draw-IR closure, but the freestanding RV64 runtime does not define that
primitive.  The final link therefore fails with an unresolved `str.parse_i64`.
This is a compiler/runtime completeness defect: an intrinsic accepted by the
language surface must either lower to a supplied freestanding definition or be
rejected for this target before link.

## Root fix

Make the LLVM native intrinsic lowering for `text.parse_i64() -> i64?` supply
a real optional result on freestanding RV64, including invalid-input and
overflow handling.  Do not solve this by adding a linker ignore rule or a
hard-coded placeholder: callers depend on `nil` to select their existing
fallback behavior.

## Acceptance

Build the canonical RV64 WM/web Draw-IR entry with the LLVM native linker and
verify that its final ELF has no unresolved `str.parse_i64` (nor a replacement
undefined parse primitive).  Run a native executable probe covering `"0"`,
`"12"`, `"-12"`, empty text, junk, and overflow; valid input must retain its
value and invalid input must return `nil` so `??` fallbacks still fire.
