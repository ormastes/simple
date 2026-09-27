# TODO — tiered JIT single-pass source scan API

- **Date:** 2026-09-27
- **Status:** OPEN
- **Area:** interpreter / tiered JIT (`src/compiler/95.interp/execution/tiered_jit.spl`)
- **Owner ruling (2026-09-27):** specs reverted to the implemented contract; the
  new API is tracked here instead of as red specs.

## What happened

`41daf6795d5` (2026-09-14, "test(jit): add lexical fact order and scan counter
specs") and its squash duplicate `8830a087a81` (2026-09-24) rewrote
`tiered_jit_hotspot_spec.spl` and `tiered_jit_source_predicate_hoist_contract_spec.spl`
and added `test/05_perf/compiler/tiered_jit_source_fact_scan_contract_spec.spl`
against an API that was never implemented. `tiered_jit.spl` is byte-identical
before and after those commits. On the Windows stage-2 lane the specs failed
with `semantic: function _jit_hotspot_backend_plugin_fact_build not found` and
`runs exactly one indexed source scan ...: expected 0 to equal 1`.

The specs are reverted to their pre-`41daf6795d5` contract (51/51 and 2/2 under
the seed). The 05_perf spec did not exist before and is removed; its full text
remains at `41daf6795d5:test/05_perf/compiler/tiered_jit_source_fact_scan_contract_spec.spl`.

## Work to do

1. Implement `_jit_hotspot_source_scan`: one indexed pass over the source that
   derives every hotspot predicate fact, in the frozen HIR fact order.
2. Make `_jit_hotspot_backend_plugin_fact_build` return a record with `.facts`
   plus scan counters (number of source scans performed), and route the
   public fact adapter through it exactly once.
3. Delete the old rescanning helper family once nothing calls it.
4. Restore the three specs from `41daf6795d5` (they are the acceptance test),
   including canonical literal families and raw overlapping / repeated /
   Unicode / NUL substring cases.

## Acceptance

The three specs from `41daf6795d5` pass under the seed and the pure-Simple
runner, and a perf measurement shows the scan count dropping to 1 per build.
