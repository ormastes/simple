# Native array map loses text ownership and provenance

Status: OPEN

## Reproduction

`test/fixtures/compiler/native_array_map_text_provenance_open_bug.spl` must
print `a,b` with default LLVM and explicit Cranelift. Current native output is
empty with exit status 0.

## Root cause

Two native MIR paths overlap:

1. Missing or misleading method metadata can resolve `Array.map` through the
   Option `map` owner.
2. The array fallback forces elements and callback results through `i64`.
   For text, integer decode/re-box drops the heap-string tag, so `join` rejects
   every mapped element.

Correctly tagged nonliteral arrays already join successfully; `join` is not the
owner of this defect.

## Acceptance

- Runtime-array provenance wins before Option/custom `map` fallback, without
  evaluating the receiver twice.
- Inline array-map callbacks preserve input and result MIR types, including the
  returned array's element type.
- Zero- or multi-parameter callbacks fail loudly; static/custom map owners are
  not stolen.
- The fixture prints `a,b` under default LLVM and explicit Cranelift.
- Focused MIR coverage observes the array loop and excludes Option-map blocks.
