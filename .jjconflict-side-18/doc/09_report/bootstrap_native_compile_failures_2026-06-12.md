# Bootstrap Native Compile Failures — 2026-06-12

`bin/simple build bootstrap` skipped 4 files as non-critical. Two were fixed at the
source level (missing type information the native HIR could not infer); two are
compiler bugs recorded here.

## Fixed in source (verified by bootstrap re-run)

| File | Error | Fix |
|------|-------|-----|
| `src/compiler/90.tools/leak_check/main.spl` | HIR: cannot infer field type for struct 'ANY' field 'alloc_id' | explicit `val leaks: [MemLeakEntry]` annotation |
| `src/compiler_rust/lib/std/src/core/math.spl` | Cranelift fcvt_to_sint type mismatch in `round()` (`floor(x + 0.5)` call boundary) | inlined floor logic on an explicitly f32-typed local |

The seed/interpreter compiles both originals fine — these are native-pipeline gaps
papered over with valid-Simple annotations/restructuring at the call site.

## Open compiler bugs

### 1. f32 array literals: bitcast 64-bit vs 32-bit (codegen)
- File: `src/lib/nogc_sync_mut/simd.spl`, `Vec4f.to_array` / `Vec8f.to_array`
- Repro: `fn to_array() -> [f32]: [self.x, self.y, self.z, self.w]` with f32 fields
- Error: `[CODEGEN VERIFY] ... inst2: The bitcast argument v2 has a type of 32 bits,
  which doesn't match an expected type of 64 bits`
- Suspected layer: array-literal lowering boxes elements as 64-bit runtime values
  without an f32→f64 (or f32→bits32) conversion on the element path.
- A source-side change would mean widening the public API to `[f64]` — rejected as a
  cover-up. Needs a codegen fix.

### 2. Generic struct field type lost during method lowering (HIR)
- File: `src/compiler_rust/lib/std/src/core/collections.spl`, `SliceIter<T>`
- Error: `hir: Unsupported feature: cannot infer field type while lowering
  SliceIter.next: struct 'SliceIter' field 'slice'`
- The struct is fully annotated (`slice: Slice<T>`); adding `SliceIter<T> { ... }`
  generic args at the construction site did not help, and a typed local
  (`val s: Slice<T> = self.slice`) inside `next()` did not help either (verified by
  bootstrap re-run 2026-06-12) — the failure is in resolving the generic field type
  of the receiver during monomorphized method lowering, so no body-level annotation
  can fix it. `MutSliceIter.next` has the identical shape and presumably the same
  bug once reached. Needs an HIR fix.

### 3. f32 arithmetic through call boundary (codegen, worked around)
- File: `src/compiler_rust/lib/std/src/core/math.spl`, `round(x: f32) -> i32`
- Original body `floor(x + 0.5)` failed ("bitcast type mismatch, i64 expected, i32
  given"); an `as f32`/`as i32` cast chain shifted the error to a Cranelift
  `fcvt_to_sint.i64` verifier failure. Inlining floor's body on an f32-typed local
  compiles clean (verified), but the underlying lowering of f32 literal arithmetic
  passed through a call returning i32 still needs a real fix — the workaround is
  flagged in a comment at the site.

## Residual

The bootstrap links `bin/simple_native` with ~38 internal symbols stubbed due to the
unresolved collections/simd references above. The 3-stage self-compilation
verification stages were not re-run in these passes.
