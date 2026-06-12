# Bootstrap Native Compile Failures — 2026-06-12

`bin/simple build bootstrap` skipped 4 files as non-critical. Two were fixed at the
source level (missing type information the native HIR could not infer); two are
compiler bugs recorded here.

## Fixed in source (this change)

| File | Error | Fix |
|------|-------|-----|
| `src/compiler/90.tools/leak_check/main.spl` | HIR: cannot infer field type for struct 'ANY' field 'alloc_id' | explicit `val leaks: [MemLeakEntry]` annotation |
| `src/compiler_rust/lib/std/src/core/collections.spl` | HIR: cannot infer field type for struct 'SliceIter' field 'slice' | explicit generic arg `SliceIter<T> { ... }` in `Slice<T>.iter()` |

Both are inference gaps in the native HIR layer: return-type propagation through a
module-level function (`parse_leak_dump`) and generic-arg inference for struct
literals inside a generic impl. The annotations are valid Simple either way, but the
seed/interpreter infers both fine — file follow-up HIR work if more sites appear.

## Open compiler bugs (codegen, f32 narrowing)

### 1. f32 array literals: bitcast 64-bit vs 32-bit
- File: `src/lib/nogc_sync_mut/simd.spl`, `Vec4f.to_array` / `Vec8f.to_array`
- Repro: `fn to_array() -> [f32]: [self.x, self.y, self.z, self.w]` with f32 fields
- Error: native codegen "bitcast type mismatch (64-bit vs 32-bit)"
- Suspected layer: array-literal lowering boxes elements as 64-bit runtime values
  without an f32→f64 (or f32→bits32) conversion on the element path.
- A source-side change would mean widening the public API to `[f64]` — rejected as a
  cover-up. Needs a codegen fix.

### 2. f32 arithmetic intermediate widened to i64
- File: `src/compiler_rust/lib/std/src/core/math.spl`, `round(x: f32) -> i32`
- Original body `floor(x + 0.5)` failed with "bitcast type mismatch (i64 expected,
  i32 given)". Worked around in this change with explicit `as f32` / `as i32` casts;
  the underlying lowering of mixed f32 literal arithmetic feeding an i32-returning
  call still needs a real fix — the workaround is flagged in a comment at the site.
