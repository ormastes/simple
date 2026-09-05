# Dns Wire Malformed Offset Specification

> Tests covering DNS wire malformed offset guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dns Wire Malformed Offset Specification

## Scenarios

### DNS wire malformed offset guards

#### returns default values for negative primitive read offsets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns default values for negative primitive read offsets
   - Expected: wire_read_u8(bytes, -1) equals `0`
   - Expected: wire_read_u16(bytes, -1) equals `0`
   - Expected: wire_read_u32(bytes, -1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns default values for negative primitive read offsets")
val bytes: [i64] = [0x12, 0x34, 0x56, 0x78]
expect(wire_read_u8(bytes, -1)).to_equal(0)
expect(wire_read_u16(bytes, -1)).to_equal(0)
expect(wire_read_u32(bytes, -1)).to_equal(0)
```

</details>

#### returns default values for truncated primitive reads

- returns default values for truncated primitive reads
   - Expected: wire_read_u16(bytes, 0) equals `0`
   - Expected: wire_read_u32(bytes, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns default values for truncated primitive reads")
val bytes: [i64] = [0x12]
expect(wire_read_u16(bytes, 0)).to_equal(0)
expect(wire_read_u32(bytes, 0)).to_equal(0)
```

</details>

#### stops malformed names before indexing out of bounds

- stops malformed names before indexing out of bounds
   - Expected: negative.0 equals ``
   - Expected: negative.1 equals `0`
   - Expected: truncated_label.0 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops malformed names before indexing out of bounds")
val negative = wire_decode_name([0], -1)
expect(negative.0).to_equal("")
expect(negative.1).to_equal(0)

val truncated_label = wire_decode_name([3, 97], 0)
expect(truncated_label.0).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DNS wire malformed offset guards.
- DNS wire malformed offset guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd87115cd0707f03cde32cfa73d7baf264a1d9b57bda98dbaa40652f4d6d9580`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd87115cd0707f03cde32cfa73d7baf264a1d9b57bda98dbaa40652f4d6d9580`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd87115cd0707f03cde32cfa73d7baf264a1d9b57bda98dbaa40652f4d6d9580`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns default values for negative primitive read offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns default values for truncated primitive reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/dns/dns_wire_malformed_offset_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stops malformed names before indexing out of bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
