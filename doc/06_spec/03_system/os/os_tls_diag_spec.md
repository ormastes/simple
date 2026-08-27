# Os Tls Diag Specification

> Tests covering TLS diag.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Tls Diag Specification

## Scenarios

### TLS diag

#### hkdf_extract changes when IKM changes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hkdf_extract changes when IKM changes
   - Expected: _bytes_eq(prk_a, prk_diff) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hkdf_extract changes when IKM changes")
val ikm_a: [u8] = [
    0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8,
    0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8,
    0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8, 0x0Bu8
]

val ikm_diff: [u8] = [
    0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8,
    0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8,
    0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8, 0xAAu8
]

val salt_a: [u8] = [
    0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8,
    0x07u8, 0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8
]

val prk_a = hkdf_extract(salt_a, ikm_a)
val prk_diff = hkdf_extract(salt_a, ikm_diff)
expect(_bytes_eq(prk_a, prk_diff)).to_equal(false)
```

</details>

#### hkdf_extract_from_list changes when IKM changes

- hkdf_extract_from_list changes when IKM changes
   - Expected: prk_a.len() equals `32`
   - Expected: prk_diff.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hkdf_extract_from_list changes when IKM changes")
var ikm_a = []
var i = 0
while i < 79:
    ikm_a.push(0x41)
    i = i + 1
ikm_a.push(0x41)

var ikm_diff = []
i = 0
while i < 79:
    ikm_diff.push(0x41)
    i = i + 1
ikm_diff.push(0x42)

var salt_a = []
salt_a.push(0x00)
salt_a.push(0x01)
salt_a.push(0x02)
salt_a.push(0x03)
salt_a.push(0x04)
salt_a.push(0x05)
salt_a.push(0x06)
salt_a.push(0x07)
salt_a.push(0x08)
salt_a.push(0x09)
salt_a.push(0x0a)
salt_a.push(0x0b)
salt_a.push(0x0c)

val prk_a = hkdf_extract_from_list(salt_a, ikm_a)
val prk_diff = hkdf_extract_from_list(salt_a, ikm_diff)
expect(prk_a.len()).to_equal(32)
expect(prk_diff.len()).to_equal(32)
```

</details>

#### hkdf_expand_label encodes a different info block than raw expand

- hkdf_expand_label encodes a different info block than raw expand
   - Expected: _bytes_eq(label_out, raw_expand) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hkdf_expand_label encodes a different info block than raw expand")
val prk_a: [u8] = [
    0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8, 0x08u8,
    0x09u8, 0x0Au8, 0x0Bu8, 0x0Cu8, 0x0Du8, 0x0Eu8, 0x0Fu8, 0x10u8,
    0x11u8, 0x12u8, 0x13u8, 0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8,
    0x19u8, 0x1Au8, 0x1Bu8, 0x1Cu8, 0x1Du8, 0x1Eu8, 0x1Fu8, 0x20u8
]
val empty_ctx: [u8] = []
val label_out = hkdf_expand_label(prk_a, "key", empty_ctx, 32)
val raw_expand = hkdf_expand(prk_a, empty_ctx, 32)
expect(_bytes_eq(label_out, raw_expand)).to_equal(false)
```

</details>

#### transcript hash changes when message bytes change

- transcript hash changes when message bytes change
   - Expected: _bytes_eq(h4, h5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transcript hash changes when message bytes change")
val t0 = transcript_new()
val h4 = transcript_hash(transcript_add(t0, [0xAAu8, 0xBBu8]))
val h5 = transcript_hash(transcript_add(t0, [0xCCu8, 0xDDu8]))
expect(_bytes_eq(h4, h5)).to_equal(false)
```

</details>

#### hmac_from_list differs when second-block bytes change

- hmac_from_list differs when second-block bytes change
   - Expected: _bytes_eq(hmac_a, hmac_b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hmac_from_list differs when second-block bytes change")
var msg_a = []
var msg_b = []
var i = 0
while i < 79:
    msg_a.push(0x41)
    msg_b.push(0x41)
    i = i + 1
msg_a.push(0x41)
msg_b.push(0x42)

val key = [
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
    0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c
]
val hmac_a = sha256_hmac_from_list(key, msg_a)
val hmac_b = sha256_hmac_from_list(key, msg_b)
expect(_bytes_eq(hmac_a, hmac_b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_diag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS diag.
- TLS diag

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6087e2fc9db2d63e06c8919496d7824cbeb3032080d0a113a076869dbe5ee64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6087e2fc9db2d63e06c8919496d7824cbeb3032080d0a113a076869dbe5ee64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6087e2fc9db2d63e06c8919496d7824cbeb3032080d0a113a076869dbe5ee64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/os_tls_diag_spec.spl
mirror: doc/06_spec/03_system/os/os_tls_diag_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_tls_diag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_tls_diag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_tls_diag_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/os_tls_diag_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hkdf_extract changes when IKM changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_diag_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hkdf_extract_from_list changes when IKM changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_diag_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hkdf_expand_label encodes a different info block than raw expand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
