# Tiered JIT source fact scan operation contract

This performance specification uses deterministic operation counters rather
than elapsed time. It proves that source work is gated by eligibility and is
bounded by source bytes, independent of the number of lexical predicates.

## Scope and evidence

| Field | Value |
|---|---|
| Source | `test/05_perf/compiler/tiered_jit_source_fact_scan_contract_spec.spl` |
| Importance | critical (weight 3), high (weight 2) |
| Oracle | private value-returned scan counters and semantic fact equality |
| Timing oracle | none; no clock, sleep, process, or timeout is used |

## Scenarios

- Typed-MIR false and safe-deopt false each produce five zero counters.
- An eligible empty source records one snapshot/pass and zero visits,
  attempts, and comparisons.
- An eligible non-empty source visits exactly `source.bytes().len()` bytes and
  stays under `96 * source_bytes_visited` comparisons.
- Repeating one source four times makes byte visits exactly four times while
  preserving the ordered fact vector.
- A source containing 64 repeated literal families remains below the same
  fixed comparison ceiling.

The operation counter is acceptance evidence for algorithmic shape, not
production telemetry or a substitute for semantic parity tests.
