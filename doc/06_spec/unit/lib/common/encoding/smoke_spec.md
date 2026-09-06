# Smoke Specification

> Tests covering impl smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Specification

## Scenarios

### impl smoke

#### encode varint 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encode varint 1
   - Expected: enc.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encode varint 1")
val enc = pb_encode_varint(1)
expect(enc.len()).to_equal(1)
```

</details>

#### decode field fixed64

- decode field fixed64
   - Expected: r[2] equals `1000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decode field fixed64")
var tb = pb_encode_tag(4, 1)
var vb = pb_encode_fixed64(1000000000000)
var out: [u8] = []
var i = 0
while i < tb.len():
    var bv: u8 = tb[i].to_i64().to_u8()
    out.push(bv)
    i = i + 1
i = 0
while i < vb.len():
    var bv: u8 = vb[i].to_i64().to_u8()
    out.push(bv)
    i = i + 1
val r = pb_decode_field(out, 0)
expect(r[2]).to_equal(1000000000000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/encoding/smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering impl smoke.
- impl smoke

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `512bd873739415c2b794dc5fa9c345b50b5fe95ba9d55da1a03be76a07e15a8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `512bd873739415c2b794dc5fa9c345b50b5fe95ba9d55da1a03be76a07e15a8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `512bd873739415c2b794dc5fa9c345b50b5fe95ba9d55da1a03be76a07e15a8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/encoding/smoke_spec.spl
mirror: doc/06_spec/unit/lib/common/encoding/smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/encoding/smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/encoding/smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/encoding/smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/encoding/smoke_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encode varint 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/smoke_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decode field fixed64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
