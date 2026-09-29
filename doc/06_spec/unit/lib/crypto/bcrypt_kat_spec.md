# bcrypt_kat_spec

> Purpose: verify the pure-Simple bcrypt (src/os/crypto/bcrypt.spl) against the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bcrypt_kat_spec

Purpose: verify the pure-Simple bcrypt (src/os/crypto/bcrypt.spl) against the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/bcrypt_kat_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: verify the pure-Simple bcrypt (src/os/crypto/bcrypt.spl) against the
jBCrypt Known-Answer Test vectors at cost=4, plus structural oracles.
Audience: crypto engineers who maintain the OS crypto library.

## Scenarios

### bcrypt jBCrypt KAT — cost=4

#### matches jBCrypt vector 1 (empty password, cost=4) byte-exactly

- Verify: jBCrypt vector 1 hashes to the published vector
   - Expected: _to_text(result) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: jBCrypt vector 1 hashes to the published vector")
# Reference: python bcrypt.hashpw(b"", salt) at cost 4; the legacy
# pending note carried an unverifiable expected string.
val expected = "$2a$04$ZjIzMjE0/RWPtJ3BDSWKWeUFMwHcw6cn92N10aRp/DxgtUb/grddq"  # oracle: python-bcrypt reference output
val salt = _decode_salt_field(expected[7:29])
val result = bcrypt_hash(_ascii(""), 4, salt)
expect(_to_text(result)).to_equal(expected)  # oracle: published KAT vector
```

</details>

#### matches jBCrypt vector 2 (password-field=password, cost=4) byte-exactly

- Verify: jBCrypt vector 2 hashes to the published vector
   - Expected: _to_text(result) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: jBCrypt vector 2 hashes to the published vector")
# Reference: python bcrypt.hashpw(b"password", salt) at cost 4
val expected = "$2a$04$ZjIzMjE0/RWPtJ3BDSWKWeux5LZcYpIu9JVIFCSDNv2Sps1f/qZHW"  # oracle: python-bcrypt reference output
val salt = _decode_salt_field(expected[7:29])
val result = bcrypt_hash(_ascii("password"), 4, salt)
expect(_to_text(result)).to_equal(expected)  # oracle: published KAT vector
```

</details>

### bcrypt base64 encoding — byte-exact intermediate check

#### zero salt encodes to 22 '.' chars at offset 7

- Verify: all-zero salt encodes as 22 alphabet-index-0 chars
   - Expected: all_dots is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: all-zero salt encodes as 22 alphabet-index-0 chars")
val salt = _salt_zeros()
val result = bcrypt_hash(_ascii("pw"), 4, salt)
# Salt occupies bytes 7..28 (22 chars). All-zero salt → 22×'.' (ASCII 46). oracle: 46 == '.'
var all_dots = true
var i: i64 = 7
while i < 29:
    if result[i] != 46u8: all_dots = false
    i = i + 1
expect(all_dots).to_equal(true)
```

</details>

### bcrypt output length and format

#### bcrypt_hash returns exactly 60 bytes

- Verify: modular crypt string length is 60
   - Expected: result.len() equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: modular crypt string length is 60")
val salt = _salt_seq()
val result = bcrypt_hash(_ascii("smoke"), 4, salt)
expect(result.len()).to_equal(60)  # oracle: $2a$ + 2 cost digits + 22 salt + 31 hash = 60
```

</details>

#### bcrypt_hash output starts with $2a$04$

- Verify: version and cost header bytes
   - Expected: result[0] equals `36u8`
   - Expected: result[1] equals `50u8`
   - Expected: result[2] equals `97u8`
   - Expected: result[3] equals `36u8`
   - Expected: result[4] equals `48u8`
   - Expected: result[5] equals `52u8`
   - Expected: result[6] equals `36u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: version and cost header bytes")
val salt = _salt_seq()
val result = bcrypt_hash(_ascii("smoke"), 4, salt)
# oracle: '$'=36 '2'=50 'a'=97 '$'=36 '0'=48 '4'=52 '$'=36
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

- Verify: identical inputs hash identically
   - Expected: _bytes_to_hex(r1) equals `_bytes_to_hex(r2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: identical inputs hash identically")
val salt = _salt_seq()
val r1 = bcrypt_hash(_ascii("hello"), 4, salt)
val r2 = bcrypt_hash(_ascii("hello"), 4, salt)
expect(_bytes_to_hex(r1)).to_equal(_bytes_to_hex(r2))
```

</details>

#### different passwords produce different hash suffixes

- Verify: password changes the digest
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: password changes the digest")
val salt = _salt_seq()
val h1 = bcrypt_hash(_ascii("abc"), 4, salt)
val h2 = bcrypt_hash(_ascii("xyz"), 4, salt)
# hash portion starts at byte 29 (oracle: 7+22 salt chars)
var same = true
var i: i64 = 29
while i < 60:
    if h1[i] != h2[i]: same = false
    i = i + 1
expect(same).to_equal(false)
```

</details>

#### different salts produce different hash suffixes

- Verify: salt changes the digest
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: salt changes the digest")
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

- Verify: correct password round-trips
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: correct password round-trips")
val salt = _salt_seq_from(7)
val hash = bcrypt_hash(_ascii("correcthorsebatterystaple"), 4, salt)
val ok = bcrypt_verify(_ascii("correcthorsebatterystaple"), hash)
expect(ok).to_equal(true)
```

</details>

#### bcrypt_verify rejects wrong password

- Verify: wrong password is rejected
   - Expected: bad is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: wrong password is rejected")
val salt = _salt_seq_from(7)
val hash = bcrypt_hash(_ascii("correcthorsebatterystaple"), 4, salt)
val bad = bcrypt_verify(_ascii("wrongpassword"), hash)
expect(bad).to_equal(false)
```

</details>

#### bcrypt_verify rejects too-short hash_string

- Verify: malformed hash string is rejected
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Verify: malformed hash string is rejected")
val short_hash = _ascii("$2a$04$too_short")
val ok = bcrypt_verify(_ascii("pw"), short_hash)
expect(ok).to_equal(false)
```

</details>

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

- Canonical SPipe generation for source `60aeffdf19aebdb5d14a1a71457fd7a28193bef91e7461f4e7e6b6e65745301b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60aeffdf19aebdb5d14a1a71457fd7a28193bef91e7461f4e7e6b6e65745301b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60aeffdf19aebdb5d14a1a71457fd7a28193bef91e7461f4e7e6b6e65745301b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/bcrypt_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/bcrypt_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/bcrypt_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/bcrypt_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/bcrypt_kat_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches jBCrypt vector 1 (empty password, cost=4) byte-exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/bcrypt_kat_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches jBCrypt vector 2 (password=password, cost=4) byte-exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/bcrypt_kat_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero salt encodes to 22 '.' chars at offset 7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
