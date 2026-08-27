# Pbkdf2 Industry Vectors Specification

> Tests covering PBKDF2-HMAC-SHA-256 industry test vectors, PBKDF2-HMAC-SHA-512 industry test vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pbkdf2 Industry Vectors Specification

## Scenarios

### PBKDF2-HMAC-SHA-256 industry test vectors

#### TC1: password-field=password salt=salt c=1 dkLen=32 → 120fb6cf...

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TC1: password-field=password salt=salt c=1 dkLen=32 → 120fb6cf...


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: password-field=password salt=salt c=1 dkLen=32 → 120fb6cf...")
# draft-josefsson-pbkdf2-test-vectors-00 §2
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 1, 32))).to_equal(
    "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"
)
```

</details>

#### TC2: password-field=password salt=salt c=2 dkLen=32 → ae4d0c95...

- TC2: password-field=password salt=salt c=2 dkLen=32 → ae4d0c95...


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: password-field=password salt=salt c=2 dkLen=32 → ae4d0c95...")
# draft-josefsson-pbkdf2-test-vectors-00 §2
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 2, 32))).to_equal(
    "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43"
)
```

</details>

#### extra: password-field=password salt=salt c=1000 dkLen=32 (perf-path coverage)

- extra: password-field=password salt=salt c=1000 dkLen=32 (perf-path coverage)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extra: password-field=password salt=salt c=1000 dkLen=32 (perf-path coverage)")
# Not an RFC vector. Exercises the c-iter fast path (cached
# SHA-256 K_ipad/K_opad prefix states + pre-built padding tail
# block). Hash cross-checked 2026-05-01 against the reference
# pre-optimisation implementation: both produce the same 32-byte
# output for these inputs at c=1000.
expect(bytes_to_hex(pbkdf2_sha256_bytes(_password(), _salt(), 1000, 32))).to_equal(
    "632c2812e46d4604102ba7618e9d6d7d2f8128f6266b4a03264d2a0460b7dcb3"
)
```

</details>

### PBKDF2-HMAC-SHA-512 industry test vectors

#### TC1: password-field=password salt=salt c=1 dkLen=64 → 867f70cf...

- TC1: password-field=password salt=salt c=1 dkLen=64 → 867f70cf...


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC1: password-field=password salt=salt c=1 dkLen=64 → 867f70cf...")
# draft-josefsson-pbkdf2-test-vectors-00 §3
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 1, 64))).to_equal(
    "867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce"
)
```

</details>

#### TC2: password-field=password salt=salt c=2 dkLen=64 → e1d9c16a...

- TC2: password-field=password salt=salt c=2 dkLen=64 → e1d9c16a...


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TC2: password-field=password salt=salt c=2 dkLen=64 → e1d9c16a...")
# draft-josefsson-pbkdf2-test-vectors-00 §3
expect(bytes_to_hex(pbkdf2_sha512_bytes(_password(), _salt(), 2, 64))).to_equal(
    "e1d9c16aa681708a45f5c7c4e215ceb66e011a2e9f0040713f18aefdb866d53cf76cab2868a39b9f7840edce4fef5a82be67335c77a6068e04112754f27ccf4e"
)
```

</details>

#### long-key: password-field=200×'A' salt=salt c=1 dkLen=64 (HMAC key>block_size)

- long-key: password-field=200×'A' salt=salt c=1 dkLen=64 (HMAC key>block_size)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("long-key: password-field=200×'A' salt=salt c=1 dkLen=64 (HMAC key>block_size)")
# Not in any RFC, but cross-checked 2026-05-01 against Python
# `hashlib.pbkdf2_hmac("sha512", b"A"*200, b"salt", 1, 64)`.
# Forces the `key > 128B → sha512_bytes(key)` branch in
# `hmac_sha512_bytes`, which the short-key reference spec does
# not cover.
expect(bytes_to_hex(pbkdf2_sha512_bytes(_long_password_sha512(), _salt(), 1, 64))).to_equal(
    "d4d976cd28931aa0d74fe2ea17c14c15b6321b6e69520106468a2812bfc79866058d097bd7c71e1c498512f66248928f162833dce24793d7203dc2d2eabe9429"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PBKDF2-HMAC-SHA-256 industry test vectors, PBKDF2-HMAC-SHA-512 industry test vectors.
- PBKDF2-HMAC-SHA-256 industry test vectors
- PBKDF2-HMAC-SHA-512 industry test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `5860017c71e8a15569014190f02e63e5a6be163b106f78b7d5c50fc289cbd6e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5860017c71e8a15569014190f02e63e5a6be163b106f78b7d5c50fc289cbd6e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5860017c71e8a15569014190f02e63e5a6be163b106f78b7d5c50fc289cbd6e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl
mirror: doc/06_spec/unit/lib/crypto/pbkdf2_industry_vectors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/pbkdf2_industry_vectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/pbkdf2_industry_vectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC1: password=password salt=salt c=1 dkLen=32 → 120fb6cf...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TC2: password=password salt=salt c=2 dkLen=32 → ae4d0c95...' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extra: password=password salt=salt c=1000 dkLen=32 (perf-path coverage)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
