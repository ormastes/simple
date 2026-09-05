# Packet Multibyte Specification

> Tests covering mqtt_encode_string multi-byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packet Multibyte Specification

## Scenarios

### mqtt_encode_string multi-byte

#### café encodes to its exact 2-byte UTF-8 wire bytes, not a truncated/garbage payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- café encodes to its exact 2-byte UTF-8 wire bytes, not a truncated/garbage payload
   - Expected: encoded.len() equals `7`
   - Expected: encoded[0] equals `0`
   - Expected: encoded[1] equals `5`
   - Expected: encoded[2] equals `99`
   - Expected: encoded[3] equals `97`
   - Expected: encoded[4] equals `102`
   - Expected: encoded[5] equals `195`
   - Expected: encoded[6] equals `169`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("café encodes to its exact 2-byte UTF-8 wire bytes, not a truncated/garbage payload")
val encoded = mqtt_encode_string("café")
# 2-byte length prefix (0, 5) + 5 payload bytes: c a f 0xC3 0xA9
expect(encoded.len()).to_equal(7)
expect(encoded[0]).to_equal(0)
expect(encoded[1]).to_equal(5)
expect(encoded[2]).to_equal(99)
expect(encoded[3]).to_equal(97)
expect(encoded[4]).to_equal(102)
expect(encoded[5]).to_equal(195)
expect(encoded[6]).to_equal(169)
```

</details>

#### pure ASCII is unaffected (regression guard)

- pure ASCII is unaffected (regression guard)
   - Expected: encoded.len() equals `4`
   - Expected: encoded[1] equals `2`
   - Expected: encoded[2] equals `104`
   - Expected: encoded[3] equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pure ASCII is unaffected (regression guard)")
val encoded = mqtt_encode_string("hi")
expect(encoded.len()).to_equal(4)
expect(encoded[1]).to_equal(2)
expect(encoded[2]).to_equal(104)
expect(encoded[3]).to_equal(105)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mqtt_encode_string multi-byte.
- mqtt_encode_string multi-byte

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `7ca344149ef484929fbb177ac4b0ad13b123dc2a550e8e3254f5aaa2039b162c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ca344149ef484929fbb177ac4b0ad13b123dc2a550e8e3254f5aaa2039b162c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ca344149ef484929fbb177ac4b0ad13b123dc2a550e8e3254f5aaa2039b162c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'café encodes to its exact 2-byte UTF-8 wire bytes, not a truncated/garbage payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure ASCII is unaffected (regression guard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
