# Source snapshot performance NFR options

<!-- codex-research -->
Status: OPTIONS. User-stated end-to-end Hello compilation target: less than 0.1 s.
This target is retained, not replaced by a narrower snapshot-only measurement.

| Option | Measurement scope | Pros | Cons | Effort |
| --- | --- | --- | --- | --- |
| N1: Full cold and warm target | Require sub-100-ms Hello compilation including cold admission, compiler and executable production; report warm separately | Directly covers all setup costs | Current runtime/link costs alone exceed target; feasibility not established | XL, cross-component investigation |
| N2: Steady-state target with cold budget pending | Require sub-100-ms actual incremental Hello compilation in an initialized workspace; report cold cost without hiding it and agree its budget separately | Reflects edit/compile workflow; isolates recurring cost | Does not satisfy the target if the user intends cold invocations too | L, controlled benchmark and invalidation suite |
| N3: Evidence baseline first | Measure cold, unchanged warm and changed-input distributions before selecting enforceable thresholds | Avoids unsupported promises; identifies exclusive costs | Interim step only; user latency target remains unmet | S/M, instrumentation and reports |

All options require compiler-only and end-to-end durations, cache-hit counts,
files/bytes processed, process launches, peak and retained memory, and actual
compiled-program outputs. Distinguish warm source snapshots from warm objects.
Do not count cached-output lookup alone as successful new compilation.

Report p50/p95 over a bounded, predefined benchmark set rather than repeatedly
rerunning passing acceptance tests. Include same-backend comparisons, source and
dependency edits, unrelated edits, runtime/toolchain/config changes, missing or
corrupt blobs, concurrent publication and interrupted builds. Record memory and
correctness regressions even when latency improves.
