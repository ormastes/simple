# Sha256 Pure Simple Specification

> Tests covering OS pure Simple SHA-256.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 Pure Simple Specification

## Scenarios

### OS pure Simple SHA-256

#### matches RFC 6234 empty-string SHA-256

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches RFC 6234 empty-string SHA-256
   - Expected: _bytes_to_hex(digest) equals `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches RFC 6234 empty-string SHA-256")
val empty: [u8] = []
val digest = sha256_with_len(empty, 0)
expect(_bytes_to_hex(digest)).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### matches RFC 6234 abc SHA-256

- matches RFC 6234 abc SHA-256
   - Expected: _bytes_to_hex(digest) equals `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches RFC 6234 abc SHA-256")
val abc: [u8] = [0x61u8, 0x62u8, 0x63u8]
val digest = sha256_with_len(abc, 3)
expect(_bytes_to_hex(digest)).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### matches RFC 4231 HMAC-SHA-256 TC1

- matches RFC 4231 HMAC-SHA-256 TC1
   - Expected: _bytes_to_hex(mac) equals `b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches RFC 4231 HMAC-SHA-256 TC1")
val data: [u8] = [0x48u8, 0x69u8, 0x20u8, 0x54u8, 0x68u8, 0x65u8, 0x72u8, 0x65u8]
val mac = sha256_hmac_with_len(_hmac_tc1_key(), 20, data, 8)
expect(_bytes_to_hex(mac)).to_equal("b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
```

</details>

#### matches the one-shot digest across ordered partial and full blocks

- matches the one-shot digest across ordered partial and full blocks
   - Expected: sha256_stream_finish(stream).unwrap() equals `sha256_with_len(data, 130u64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the one-shot digest across ordered partial and full blocks")
var data: [u8] = []
var index: i64 = 0
while index < 130:
    data.push((index & 0xff) as u8)
    index = index + 1
var first: [u8] = []
var second: [u8] = []
var third: [u8] = []
index = 0
while index < 7:
    first.push(data[index])
    index = index + 1
while index < 71:
    second.push(data[index])
    index = index + 1
while index < data.len():
    third.push(data[index])
    index = index + 1
val stream = sha256_stream_new()
sha256_stream_update(stream, first).unwrap()
sha256_stream_update(stream, second).unwrap()
sha256_stream_update(stream, third).unwrap()
expect(sha256_stream_finish(stream).unwrap()).to_equal(sha256_with_len(data, 130u64))
```

</details>

#### handles empty input and the two-block final-padding boundary

- handles empty input and the two-block final-padding boundary
   - Expected: _bytes_to_hex(sha256_stream_finish(sha256_stream_new()).unwrap()) equals `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
   - Expected: sha256_stream_finish(stream).unwrap() equals `sha256_with_len(data, 60u64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty input and the two-block final-padding boundary")
expect(_bytes_to_hex(sha256_stream_finish(sha256_stream_new()).unwrap())).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
var data: [u8] = []
var index: i64 = 0
while index < 60:
    data.push(0x61u8)
    index = index + 1
val stream = sha256_stream_new()
sha256_stream_update(stream, data).unwrap()
expect(sha256_stream_finish(stream).unwrap()).to_equal(sha256_with_len(data, 60u64))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/sha256_pure_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OS pure Simple SHA-256.
- OS pure Simple SHA-256

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b33ca432a83bee35dd36854abf525480341f10327de92e4ee32a704d5d12d344`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b33ca432a83bee35dd36854abf525480341f10327de92e4ee32a704d5d12d344`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b33ca432a83bee35dd36854abf525480341f10327de92e4ee32a704d5d12d344`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/crypto/sha256_pure_simple_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/sha256_pure_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/sha256_pure_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/sha256_pure_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/sha256_pure_simple_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches RFC 6234 empty-string SHA-256' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/sha256_pure_simple_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches RFC 6234 abc SHA-256' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/sha256_pure_simple_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches RFC 4231 HMAC-SHA-256 TC1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
