# Compiler native-capsule symbol-sort feature expert

## Role

Own lane-specific knowledge for deterministic `SymbolId` ordering during
frozen native-capsule identity generation. This is an LLM wiki entry, not a
shared executable Codex/Claude skill and not authority to modify global skills.

## Code and evidence map

| Concern | Path |
|---|---|
| Production sorter and capsule identity | `src/compiler/80.driver/driver_types.spl` |
| Focused microbenchmark | `test/05_perf/compiler/native_capsule_symbol_sort_bench.spl` |
| Retained measurements | `doc/09_report/perf/compiler_native_capsule_symbol_sort_microbenchmark_2026-08-16.md` |
| System SSpec | `test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl` |
| Manual mirror | `doc/06_spec/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.md` |
| Test plan and REQ matrix | `doc/03_plan/sys_test/compiler_native_capsule_symbol_sort.md` |
| Lane state | `.spipe/compiler_native_capsule_symbol_sort/state.md` |
| Operator guide | `doc/07_guide/compiler/check_perf.md` |

## Invariants

- Sort ascending by the numeric `SymbolId.id` only.
- Preserve every input value and caller-visible value semantics.
- Equal IDs select the left merge run, keeping deterministic stable behavior.
- Empty and singleton arrays return without indexing.
- Non-power-of-two sizes must merge the final partial run without reading past
  the array.
- The implementation stays typed `[SymbolId]`; do not route it through generic
  `Any` sorting until native dispatch is independently admitted.
- Performance evidence uses a checksum and correctness gate outside the timed
  region; no failed or incomplete output may be recorded as a speedup.

## Why this implementation exists

The prior selection-style nested scan performed `O(n^2)` comparisons while
hashing frozen MIR capsule maps. Lane B replaced it with a typed bottom-up
mergesort: `O(n log n)` comparisons and `O(n)` auxiliary storage. On the
retained 4,096-symbol/five-sort criterion, the final median was 19,639 µs
against one retained 11,607,363 µs baseline sample. Treat the report's
single-sample baseline caveat as load-bearing; do not manufacture baseline
p50/p95 values.

## Load-bearing test traps

1. Endpoint-only checks are insufficient; `[0, 1, 1, 3]` retains expected
   endpoints while corrupting the interior.
2. Power-of-two-only workloads miss the partial-tail merge path; retain the
   4,097-element scenario.
3. A positive checksum without full positional validation can hide duplicate
   or missing IDs.
4. Generic `array_sort_by` previously compiled but failed at runtime through a
   non-text `str.push` dispatch gap. That attempt is not evidence.
5. Bootstrap Stage 2 can support focused compiler builds but cannot certify the
   full SSpec runner, docgen, maintenance scores, Stage 4, or release.
6. A missing qualified CLI is TEST_BLOCKED, never a reason to use the Rust seed
   or mark scenarios green from source inspection.

## Requirements

- REQ-CNSS-001: deterministic order and value retention.
- REQ-CNSS-002: complete boundary/tail handling.
- REQ-CNSS-003: fail-closed full-result auditing.
- NFR-CNSS-001: measured algorithmic improvement without a flaky test timeout.

## Qualified verification

Only after an admitted current-source pure-Simple Stage 4/5 CLI passes bounded
identity and `test --help` probes:

```text
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=interpreter
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --mode=native
bin/simple spipe-docgen test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/compiler/feature/native_capsule_symbol_sort_spec.spl --baseline
```

Require nine executed examples, zero failures, no fallback/stub markers,
docgen `0 stubs`, current mirror state, and no blocker-capped `SSDOC-*`
findings. Run each acceptance command once per qualified session.

## Update rule

Refresh this page whenever the sorter algorithm, capsule identity ordering,
benchmark workload, REQ matrix, admitted runtime status, or SSpec/manual paths
change. Keep this lane-owned page separate from shared global skill trees.
