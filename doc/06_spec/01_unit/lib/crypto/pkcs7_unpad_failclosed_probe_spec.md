# Pkcs7 Unpad Failclosed Probe Specification

> Tests covering pkcs7_unpad fail-closed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pkcs7 Unpad Failclosed Probe Specification

## Scenarios

### pkcs7_unpad fail-closed

#### rejects a block of 0x99 bytes (invalid padding)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a block of 0x99 bytes (invalid padding)
   - Expected: out == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a block of 0x99 bytes (invalid padding)")
val out = pkcs7_unpad(_all_0x99_block(), 16)
expect(out == nil).to_equal(true)
```

</details>

#### rejects a trailer whose bytes disagree with the pad length

- rejects a trailer whose bytes disagree with the pad length
   - Expected: pkcs7_unpad(b, 16) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a trailer whose bytes disagree with the pad length")
# 14 data bytes + [0x02, 0x03] -> last byte says 3, run is not 3x0x03
var b: [i64] = []
var i = 0
while i < 14:
    b.push(0x41)
    i = i + 1
b.push(0x02)
b.push(0x03)
expect(pkcs7_unpad(b, 16) == nil).to_equal(true)
```

</details>

#### rejects a non-block-multiple length

- rejects a non-block-multiple length
   - Expected: pkcs7_unpad(b, 16) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-block-multiple length")
var b: [i64] = []
var i = 0
while i < 15:
    b.push(0x01)
    i = i + 1
expect(pkcs7_unpad(b, 16) == nil).to_equal(true)
```

</details>

#### rejects an empty input

- rejects an empty input
   - Expected: pkcs7_unpad(e, 16) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty input")
var e: [i64] = []
expect(pkcs7_unpad(e, 16) == nil).to_equal(true)
```

</details>

#### round-trips valid padding

- round-trips valid padding
   - Expected: padded.len() equals `16`
   - Expected: back.len() equals `5`
   - Expected: back[0] equals `0x61`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips valid padding")
var msg: [i64] = []
var i = 0
while i < 5:
    msg.push(0x61 + i)
    i = i + 1
val padded_opt = pkcs7_pad(msg, 16)
if val padded = padded_opt:
    expect(padded.len()).to_equal(16)
    val back_opt = pkcs7_unpad(padded, 16)
    if val back = back_opt:
        expect(back.len()).to_equal(5)
        expect(back[0]).to_equal(0x61)
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pkcs7_unpad fail-closed.
- pkcs7_unpad fail-closed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c17985fa3460144f1ec7192a37f934d67099652a280e913dd9051ade5b4f0e52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c17985fa3460144f1ec7192a37f934d67099652a280e913dd9051ade5b4f0e52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c17985fa3460144f1ec7192a37f934d67099652a280e913dd9051ade5b4f0e52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a block of 0x99 bytes (invalid padding)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a trailer whose bytes disagree with the pad length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/pkcs7_unpad_failclosed_probe_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a non-block-multiple length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
