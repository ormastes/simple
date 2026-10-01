# Crc32 Text C Vs Simple Perf Specification

> Tests covering crc32_text C vs Simple perf (interpreter lane).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crc32 Text C Vs Simple Perf Specification

## Scenarios

### crc32_text C vs Simple perf (interpreter lane)

#### records the measured ratio and bounds interpreter-lane cost

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records the measured ratio and bounds interpreter-lane cost


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("records the measured ratio and bounds interpreter-lane cost")
var body = ""
var i = 0
while i < 50:
    body = body + "row-{i}|payload-abcdefghijklmnopqrstuvwxyz|"
    i = i + 1
val iters = 200
val c_ms = bench(iters, body, false)
val s_ms = bench(iters, body, true)
print("perf_evidence: lane=interpreter iters={iters} body_len={body.len()} c_us={c_ms} simple_us={s_ms}")
# Outputs must agree or the timing compares different work.
assert_equal(crc32_text(body), rt_crc32_text(body))
# Interpreter-lane sanity ceiling only (NOT a parity verdict).
# Measured 2026-08-18 on this box: O(n^2) byte-array rebuild = 1185x
# the C oracle; linear streaming = 640x (both at body_len 2090,
# iters 200). 1000x sits between them: it fails the accidental-
# quadratic class while accepting the documented interpreter envelope
# (~100-1000x vs native). Native-lane parity gate is tracked in
# c_migration_inventory.sdn (perf_status: pending_native_lane).
assert_true(s_ms <= (c_ms + 1) * 1000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering crc32_text C vs Simple perf (interpreter lane).
- crc32_text C vs Simple perf (interpreter lane)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
- `REQ-C-MIG-CRC32-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59102648c270500a1734f75071f148457e46c7159cae1848baa1175e3f5e52df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59102648c270500a1734f75071f148457e46c7159cae1848baa1175e3f5e52df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59102648c270500a1734f75071f148457e46c7159cae1848baa1175e3f5e52df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl
mirror: doc/06_spec/05_perf/lib/crc32_text_c_vs_simple_perf_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/05_perf/lib/crc32_text_c_vs_simple_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/lib/crc32_text_c_vs_simple_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the measured ratio and bounds interpreter-lane cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
