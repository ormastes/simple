# Parser Framework — System Spec Plan

## Scope

- Cover canonical scalar parser behavior in one executable scenario file: `test/03_system/app/compiler/feature/parser_framework_spec.spl`.
- Ensure new module surfaces in `src/lib/common/structural/parse` and `src/lib/nogc_async_mut/structural/parse` are exercised by direct scenario assertions and available for follow-on SIMD/GPU/incremental work.

## Scenarios

1. `parser-framework baseline`
   - deterministic CPU-reference hash stability for repeated equivalent parses
   - hybrid mode demotion parity when accelerated mode is requested
   - malformed lex program hard reject behavior

## Evidence

- Source executable: `test/03_system/app/compiler/feature/parser_framework_spec.spl`
- Generated manual: `doc/06_spec/03_system/app/compiler/feature/parser_framework_spec.md`
- Requirement mapping: AC-2, AC-3, AC-9, AC-10

## Notes

- This is a wave-0/1 parity gate only.
- SIMD/GPU/incremental scenarios are explicitly out-of-scope for this baseline spec and should be added as additional executable specs before final AC completion.
