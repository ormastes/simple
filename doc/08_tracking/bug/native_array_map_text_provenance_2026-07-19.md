# Native array map loses text ownership and provenance

Status: SOURCE FIXED; native execution pending

Verification attempt 2026-11-25 (worktree wt-p3-bas, Windows x86_64, tracked
self-hosted `bin/simple.exe`): source fix re-confirmed present —
`lower_array_map` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:7672` inlines
the callback (`lower_inline_lambda_with_locals`), derives
`mapped_elem_type` from the callback result, and re-types the result array
(`MirTypeKind.Array(mapped_elem_type, 0)`), matching the 2026-11-04 triage.
Interpreter run of the fixture prints the expected `a,b`. The native half of
the acceptance is environment-blocked here: `SIMPLE_LIB=src bin/simple.exe
native-build test/fixtures/compiler/native_array_map_text_provenance_open_bug.spl
--output ...` produced no artifact and was killed by a 480s timeout
(exit 124) after stalling in the `80.driver` AOT native-output phase (log
stopped growing ~3 min in). Native LLVM/Cranelift execution of the fixture
(`a,b` under both backends) still needs a working native-build lane, e.g. a
Linux stage3 host. Status unchanged.

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

## Triage 2026-11-04 (mir slice 16)
Source fix present on origin/release/1.0.0: `lower_array_map` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` builds the
mapped array type from the callback result. Status fix-implemented-verification-pending.
Verify (needs stage3 native-build): build `test/fixtures/compiler/native_array_map_text_provenance_open_bug.spl`
with default LLVM and `--backend cranelift`; expected output `a,b`.
