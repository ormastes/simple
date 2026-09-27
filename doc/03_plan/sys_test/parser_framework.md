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

## Canonical Simple scalar qualification (planned, not yet passing)

The existing parser framework spec proves the lexical foundation, not Simple grammar/action or AST/HIR parity. The canonical scalar provider design is `doc/05_design/compiler/canonical_scalar_simple_grammar_action_provider_2026-09-27.md`. Extend executable coverage only when the production grammar/action owner and independent normalized comparator exist; keep incomplete scenarios fail-fast.

| Requirement | Operator flow and assertion | Executable owner |
|---|---|---|
| Parser REQ-002/003, NFR-001 | Parse the same valid and malformed Simple fixtures in isolated legacy and canonical sessions; compare ordered tokens, regions, action events, AST/HIR projection, byte spans, source maps, diagnostic order, invalidation and semantic hash. | `test/03_system/app/compiler/feature/parser_framework_spec.spl` |
| Parser REQ-008, platform REQ-003/004, EODL REQ-008 | Admit the legacy `FrontendFacetV1` adapter and prove its source generation and results remain independently observable after candidate execution. | `test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl` REQ-008 |
| EODL REQ-009 | Refuse a partial Simple dialect, stale schema or absent parity receipt; admit a complete scalar candidate only after the corpus and resource gates pass; reject SIMD promotion without scalar evidence. | `test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl` REQ-009 |
| Parser NFR-002/003 | On pinned source, binary and fixture identities, record median scalar latency, peak parser RSS and allocation counts against the retained legacy baseline. | Benchmark receipt linked from this plan before admission |

Required fixtures include reset-valid/invalid and append-valid/isolated-invalid smoke cases, then declarations, nested expressions and types, generics, Unicode and malformed UTF, indentation, interpolation, custom blocks, preprocessing, multi-error recovery, repeated reset, multifile append, and changed earlier lexical state with downstream invalidation. A missing grammar action or fallback execution is a failed candidate row. Generated manual updates follow executable spec changes and may not claim a pass before source-matched runs.
