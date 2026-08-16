# Compiler native-capsule symbol-sort system-test plan

## Status

**TEST_BLOCKED** for runtime execution, SPipe docgen, and `sspec-maintain` on
2026-08-16. The isolated lane has no `bin/simple`, no admitted Stage 4/5
full-CLI artifact was found, and the admitted pure-Simple Stage 2 compiler used
for focused performance evidence exposes only `compile` and `native-build`.
Neither the Rust seed nor the unadmitted deployed wrapper may replace the
qualified CLI.

The executable SSpec and manual mirror are complete for future execution.
Static quality and repository guards are required now and are recorded in the
lane state.

## Scope

The spec exercises `native_capsule_sorted_symbol_ids_v1` through its real
compiler module boundary:

- deterministic ascending order and input value semantics;
- empty, singleton, duplicate/negative, and 4,097-element partial-tail shapes;
- full-sequence cardinality, position, and checksum auditing that rejects
  missing or interior-corrupted results.

Excluded: flaky wall-clock thresholds, whole-compiler speed claims, Stage 4
construction/admission, release verification, the Rust seed, and any private
parallel sorting path. Performance evidence remains in
`doc/09_report/perf/compiler_native_capsule_symbol_sort_microbenchmark_2026-08-16.md`.

## Requirements

- **REQ-CNSS-001:** Native-capsule symbol ordering is deterministic ascending
  by `SymbolId.id`, retains every value, and does not mutate caller input.
- **REQ-CNSS-002:** The sorter handles empty, singleton, duplicate/negative,
  and non-power-of-two partial-tail workloads without out-of-bounds behavior or
  dropped symbols.
- **REQ-CNSS-003:** The system oracle fails closed on wrong cardinality or any
  interior ID mismatch and reports a concrete error code.
- **NFR-CNSS-001:** The retained 4,096-symbol benchmark demonstrates the
  quadratic-to-merge-sort performance criterion; SSpec verifies behavior at
  4,097 elements without embedding a host-sensitive timing threshold.

## Traceability

| Requirement | Executable spec | Manual mirror | Scenarios | Coverage |
|---|---|---|---:|---|
| REQ-CNSS-001 | `test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl` | `doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md` | reverse/value semantics; ordered; mixed duplicate/negative | Full |
| REQ-CNSS-002 | same | same | empty; singleton; 4,097 partial tail | Full |
| REQ-CNSS-003 | same | same | accepted checksum; missing result; interior corruption | Full |
| NFR-CNSS-001 | same + retained performance report | same | 4,097 behavioral stress; measured report | Full, runtime pending |

## Qualified execution order

Run each command at most once after a full CLI has an explicit self-hosted
Stage 4/5 admission receipt and passes bounded identity plus `test --help` ABI
probes:

1. `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=interpreter`
2. `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=native`
3. `bin/simple spipe-docgen test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --output doc/06_spec --no-index`
4. `bin/simple sspec-maintain scan test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --baseline`

Pass requires nine executed examples, zero failures, no fallback/stub markers,
docgen completeness with `0 stubs`, a current mirror, and no blocker-capped
`SSDOC-*` findings. Timeout, signal exit, zero executed examples, missing
summary, stale mirror, or unqualified runtime is FAIL/TEST_BLOCKED, never PASS.

## Manual rendering and evidence policy

All nine scenarios remain visible and grouped as deterministic ordering, merge
boundaries, and fail-closed auditing. Setup/checker helpers remain folded in
the executable-source section when docgen is available. No screenshots are
needed; this is semantic text/API evidence. The manual must retain runtime
provenance, TEST_BLOCKED status, exact commands, and the distinction between
behavioral SSpec coverage and the retained microbenchmark.

## Risks

- Generic `array_sort_by` previously hit a native `Any` dispatch gap; the
  production implementation must remain typed.
- Endpoint-only assertions can miss interior corruption; full positional audit
  is mandatory.
- Power-of-two-only fixtures miss partial merge tails; 4,097 is mandatory.
- A bootstrap-only Stage 2 compiler cannot certify the full SSpec runner,
  docgen, or maintenance pipeline.
