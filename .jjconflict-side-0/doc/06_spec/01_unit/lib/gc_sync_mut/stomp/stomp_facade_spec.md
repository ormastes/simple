# Stomp Facade Specification

> Tests covering gc_sync_mut STOMP facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stomp Facade Specification

## Scenarios

### gc_sync_mut STOMP facades

#### re-exports constants and heartbeat helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports constants and heartbeat helpers
   - Expected: stomp_cmd_connect() equals `CONNECT`
   - Expected: stomp_cmd_send() equals `SEND`
   - Expected: stomp_header_destination() equals `destination`
   - Expected: stomp_ack_client() equals `client`
   - Expected: stomp_null_byte() equals `\0`
   - Expected: heartbeat[0] equals `1000`
   - Expected: heartbeat[1] equals `2000`
   - Expected: format_heartbeat(1000, 2000) equals `1000,2000`
   - Expected: negotiated[0] equals `2000`
   - Expected: negotiated[1] equals `1000`
   - Expected: is_heartbeat_disabled(parse_heartbeat("0,0")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports constants and heartbeat helpers")
expect(stomp_cmd_connect()).to_equal("CONNECT")
expect(stomp_cmd_send()).to_equal("SEND")
expect(stomp_header_destination()).to_equal("destination")
expect(stomp_ack_client()).to_equal("client")
expect(stomp_null_byte()).to_equal("\0")

val heartbeat = parse_heartbeat("1000,2000")
expect(heartbeat[0]).to_equal(1000)
expect(heartbeat[1]).to_equal(2000)
expect(format_heartbeat(1000, 2000)).to_equal("1000,2000")

val negotiated = negotiate_heartbeat(parse_heartbeat("1000,1000"), parse_heartbeat("500,2000"))
expect(negotiated[0]).to_equal(2000)
expect(negotiated[1]).to_equal(1000)
expect(is_heartbeat_disabled(parse_heartbeat("0,0"))).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_sync_mut STOMP facades.
- gc_sync_mut STOMP facades

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b8b5855c86b5aa14c348000f964a03fa4ad9917cc082d3bcde371dd608d0c77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b8b5855c86b5aa14c348000f964a03fa4ad9917cc082d3bcde371dd608d0c77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b8b5855c86b5aa14c348000f964a03fa4ad9917cc082d3bcde371dd608d0c77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_sync_mut/stomp/stomp_facade_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports constants and heartbeat helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
