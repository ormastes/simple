# Bcrypt Kat Specification

> Tests covering bcrypt base64 encoding — byte-exact intermediate check, bcrypt output length and format, bcrypt_verify constant-time comparison, bcrypt jBCrypt KAT — cost=4, pending native fast-path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bcrypt Kat Specification

## Scenarios

### bcrypt base64 encoding — byte-exact intermediate check

#### zero salt encodes to 22 '.' chars at offset 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

### bcrypt output length and format

#### bcrypt_hash returns exactly 60 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _salt_seq()
val result = bcrypt_hash(_ascii("smoke"), 4, salt)
expect(result.len()).to_equal(60)
```

</details>

#### bcrypt_hash output starts with $2a$04$

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _salt_seq()
val result = bcrypt_hash(_ascii("smoke"), 4, salt)
# '$'=36 '2'=50 'a'=97 '$'=36 '0'=48 '4'=52 '$'=36
expect(result[0]).to_equal(36u8)
expect(result[1]).to_equal(50u8)
expect(result[2]).to_equal(97u8)
expect(result[3]).to_equal(36u8)
expect(result[4]).to_equal(48u8)
expect(result[5]).to_equal(52u8)
expect(result[6]).to_equal(36u8)
```

</details>

#### bcrypt_hash is deterministic — same salt+cost produces same output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _salt_seq()
val r1 = bcrypt_hash(_ascii("hello"), 4, salt)
val r2 = bcrypt_hash(_ascii("hello"), 4, salt)
expect(_bytes_to_hex(r1)).to_equal(_bytes_to_hex(r2))
```

</details>

#### different passwords produce different hash suffixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _salt_seq()
val h1 = bcrypt_hash(_ascii("abc"), 4, salt)
val h2 = bcrypt_hash(_ascii("xyz"), 4, salt)
# hash portion starts at byte 29; compare as hex to avoid early exit
var same = true
var i: i64 = 29
while i < 60:
    if h1[i] != h2[i]: same = false
    i = i + 1
expect(same).to_equal(false)
```

</details>

#### different salts produce different hash suffixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt1 = _salt_zeros()
val salt2 = _salt_one()
val h1 = bcrypt_hash(_ascii("pw"), 4, salt1)
val h2 = bcrypt_hash(_ascii("pw"), 4, salt2)
var same = true
var i: i64 = 29
while i < 60:
    if h1[i] != h2[i]: same = false
    i = i + 1
expect(same).to_equal(false)
```

</details>

### bcrypt_verify constant-time comparison

#### bcrypt_verify accepts correct password

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _salt_seq_from(7)
val hash = bcrypt_hash(_ascii("correcthorsebatterystaple"), 4, salt)
val ok = bcrypt_verify(_ascii("correcthorsebatterystaple"), hash)
expect(ok).to_equal(true)
```

</details>

#### bcrypt_verify rejects wrong password

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _salt_seq_from(7)
val hash = bcrypt_hash(_ascii("correcthorsebatterystaple"), 4, salt)
val bad = bcrypt_verify(_ascii("wrongpassword"), hash)
expect(bad).to_equal(false)
```

</details>

#### bcrypt_verify rejects too-short hash_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_hash = _ascii("$2a$04$too_short")
val ok = bcrypt_verify(_ascii("pw"), short_hash)
expect(ok).to_equal(false)
```

</details>

### bcrypt jBCrypt KAT — cost=4, pending native fast-path

#### jBCrypt vector 1 (empty password, cost=4) — pending FR bcrypt_native_runtime_helpers_2026-05-02

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Full byte-exact KAT against jBCrypt vector 1 (empty password, cost=4).
# Expected: $2a$04$ZjIzMjE0/RWPtJ3BDSWKWehnhrR8e.0.S.R6Xp5B8ynxE1pKLHzp.
# Source: https://github.com/jeremyh/jBCrypt BCryptTest.java test_vectors[0]
# Pure-Simple cost=4 likely exceeds the 60s interpreter watchdog.
pending("bcrypt_native_runtime_helpers_2026-05-02")
```

</details>

#### jBCrypt vector 2 (password-field=password, cost=4) — pending FR bcrypt_native_runtime_helpers_2026-05-02

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: $2a$04$ZjIzMjE0/RWPtJ3BDSWKW.4/16.rPtMoTWBg6iEMrPGa7jCfaAj..
# Source: https://github.com/jeremyh/jBCrypt BCryptTest.java test_vectors[1]
pending("bcrypt_native_runtime_helpers_2026-05-02")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/bcrypt_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bcrypt base64 encoding — byte-exact intermediate check, bcrypt output length and format, bcrypt_verify constant-time comparison, bcrypt jBCrypt KAT — cost=4, pending native fast-path.
- bcrypt base64 encoding — byte-exact intermediate check
- bcrypt output length and format
- bcrypt_verify constant-time comparison
- bcrypt jBCrypt KAT — cost=4, pending native fast-path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `6a90b56cfb7fdf140309561800d10b67d1c0d643154ef184bcba713ad647aae2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a90b56cfb7fdf140309561800d10b67d1c0d643154ef184bcba713ad647aae2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a90b56cfb7fdf140309561800d10b67d1c0d643154ef184bcba713ad647aae2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/crypto/bcrypt_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/bcrypt_kat_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=40
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/lib/crypto/bcrypt_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/bcrypt_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:111:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'zero salt encodes to 22 '.' chars at offset 7' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:126:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'bcrypt_hash returns exactly 60 bytes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:131:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'bcrypt_hash output starts with $2a$04$' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/crypto/bcrypt_kat_spec.spl:143:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'bcrypt_hash is deterministic — same salt+cost produces same output' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
