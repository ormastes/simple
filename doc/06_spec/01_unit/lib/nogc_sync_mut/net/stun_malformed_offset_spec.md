# Stun Malformed Offset Specification

> Tests covering STUN malformed offset guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stun Malformed Offset Specification

## Scenarios

### STUN malformed offset guards

#### rejects negative header offsets without indexing before the buffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative header offsets without indexing before the buffer
   - Expected: _is_header_error(stun_parse_header(_valid_header(), -1)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects negative header offsets without indexing before the buffer")
expect(_is_header_error(stun_parse_header(_valid_header(), -1))).to_equal(true)
```

</details>

#### ignores malformed attribute decode ranges without indexing out of bounds

- ignores malformed attribute decode ranges without indexing out of bounds
   - Expected: negative_offset_attrs.len() equals `0`
   - Expected: too_long_attrs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores malformed attribute decode ranges without indexing out of bounds")
val bytes = _valid_header()
val negative_offset_attrs = stun_decode_attributes(bytes, -1, 4)
val too_long_attrs = stun_decode_attributes(bytes, 18, 8)
expect(negative_offset_attrs.len()).to_equal(0)
expect(too_long_attrs.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering STUN malformed offset guards.
- STUN malformed offset guards

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

- Canonical SPipe generation for source `305612aa7ae605765411bdf635e3c46f750eebfcdb8c39ac0fdc514df50681fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `305612aa7ae605765411bdf635e3c46f750eebfcdb8c39ac0fdc514df50681fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `305612aa7ae605765411bdf635e3c46f750eebfcdb8c39ac0fdc514df50681fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative header offsets without indexing before the buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/net/stun_malformed_offset_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores malformed attribute decode ranges without indexing out of bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
