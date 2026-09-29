# Pbkdf2 Native Perf Specification

> Tests covering PBKDF2 native runtime helpers — SHA-256, PBKDF2 native runtime helpers — SHA-384, PBKDF2 native runtime helpers — SHA-512.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pbkdf2 Native Perf Specification

## Scenarios

### PBKDF2 native runtime helpers — SHA-256

#### TC1: c=1 dkLen=32 (regression guard, native path)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TC1: c=1 dkLen=32 (regression guard, native path)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: c=1 dkLen=32 (regression guard, native path)")
# draft-josefsson-pbkdf2-test-vectors-00 §2 TC1
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 1, 32))).to_equal(
    "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"
)
```

</details>

#### TC2: c=2 dkLen=32 (regression guard, native path)

- TC2: c=2 dkLen=32 (regression guard, native path)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: c=2 dkLen=32 (regression guard, native path)")
# draft-josefsson-pbkdf2-test-vectors-00 §2 TC2
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 2, 32))).to_equal(
    "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43"
)
```

</details>

#### extra: c=1000 dkLen=32 (P Wave-4 perf path regression guard)

- extra: c=1000 dkLen=32 (P Wave-4 perf path regression guard)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extra: c=1000 dkLen=32 (P Wave-4 perf path regression guard)")
# Hash from pbkdf2_industry_vectors_spec.spl — must remain byte-exact
# after the native short-circuit takes over the public entry point.
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 1000, 32))).to_equal(
    "632c2812e46d4604102ba7618e9d6d7d2f8128f6266b4a03264d2a0460b7dcb3"
)
```

</details>

#### TC3: c=4096 dkLen=32 (was 78s pure-Simple — AC-1)

- TC3: c=4096 dkLen=32 (was 78s pure-Simple — AC-1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC3: c=4096 dkLen=32 (was 78s pure-Simple — AC-1)")
# draft-josefsson-pbkdf2-test-vectors-00 §2 TC3.
# This is the headline AC-1 vector. Without the native extern this
# took ~78 s in interpreter mode; with rt_pbkdf2_hmac_sha256 it
# completes in <100 ms.
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 4096, 32))).to_equal(
    "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"
)
```

</details>

### PBKDF2 native runtime helpers — SHA-384

#### c=1 dkLen=48 (cross-checked vs hashlib.pbkdf2_hmac sha384)

- c=1 dkLen=48 (cross-checked vs hashlib.pbkdf2_hmac sha384)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("c=1 dkLen=48 (cross-checked vs hashlib.pbkdf2_hmac sha384)")
# Cross-checked 2026-05-01 against
#   hashlib.pbkdf2_hmac("sha384", b"password", b"salt", 1, 48).hex()
expect(bytes_to_hex(pbkdf2_sha384_bytes(_password(), _salt(), 1, 48))).to_equal(
    "c0e14f06e49e32d73f9f52ddf1d0c5c7191609233631dadd76a567db42b78676b38fc800cc53ddb642f5c74442e62be4"
)
```

</details>

#### c=4096 dkLen=48 (perf path — native only)

- c=4096 dkLen=48 (perf path — native only)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("c=4096 dkLen=48 (perf path — native only)")
# Cross-checked 2026-05-01 against
#   hashlib.pbkdf2_hmac("sha384", b"password", b"salt", 4096, 48).hex()
# SHA-384 has no pure-Simple reference impl — this must run via the
# rt_pbkdf2_hmac_sha384 extern.
expect(bytes_to_hex(pbkdf2_sha384_bytes(_password(), _salt(), 4096, 48))).to_equal(
    "559726be38db125bc85ed7895f6e3cf574c7a01c080c3447db1e8a76764deb3c307b94853fbe424f6488c5f4f1289626"
)
```

</details>

### PBKDF2 native runtime helpers — SHA-512

#### TC1: c=1 dkLen=64 (regression guard, native path)

- TC1: c=1 dkLen=64 (regression guard, native path)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: c=1 dkLen=64 (regression guard, native path)")
# draft-josefsson-pbkdf2-test-vectors-00 §3 TC1
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 1, 64))).to_equal(
    "867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce"
)
```

</details>

#### TC2: c=2 dkLen=64 (regression guard, native path)

- TC2: c=2 dkLen=64 (regression guard, native path)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: c=2 dkLen=64 (regression guard, native path)")
# draft-josefsson-pbkdf2-test-vectors-00 §3 TC2
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 2, 64))).to_equal(
    "e1d9c16aa681708a45f5c7c4e215ceb66e011a2e9f0040713f18aefdb866d53cf76cab2868a39b9f7840edce4fef5a82be67335c77a6068e04112754f27ccf4e"
)
```

</details>

#### c=80000 dkLen=64 (was >5 min pure-Simple — AC-2)

- c=80000 dkLen=64 (was >5 min pure-Simple — AC-2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("c=80000 dkLen=64 (was >5 min pure-Simple — AC-2)")
# Cross-checked 2026-05-01 against
#   hashlib.pbkdf2_hmac("sha512", b"password", b"salt", 80000, 64).hex()
# This ran at >5 min in pure-Simple; native completes in well under
# 1 s. AC-2 of FR pbkdf2_native_runtime_helpers_2026-05-01.md.
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 80000, 64))).to_equal(
    "929c53a20755e55d315d72f75bd1b28836941fa991eb6d4ac7809e01a9fd8ef17167f6206c49e47904487c1faa461bd73d210edda7b52339366cca2fff78041d"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PBKDF2 native runtime helpers — SHA-256, PBKDF2 native runtime helpers — SHA-384, PBKDF2 native runtime helpers — SHA-512.
- PBKDF2 native runtime helpers — SHA-256
- PBKDF2 native runtime helpers — SHA-384
- PBKDF2 native runtime helpers — SHA-512

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `af589e26e02e95c8add32271c6f17eff70f01aa57cfd16eac67bf78e6f712015`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af589e26e02e95c8add32271c6f17eff70f01aa57cfd16eac67bf78e6f712015`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af589e26e02e95c8add32271c6f17eff70f01aa57cfd16eac67bf78e6f712015`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1: c=1 dkLen=32 (regression guard, native path)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC2: c=2 dkLen=32 (regression guard, native path)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extra: c=1000 dkLen=32 (P Wave-4 perf path regression guard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
