# Base58 Specification

> Tests covering Base58 encode, Base58 decode, Base58Check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base58 Specification

## Scenarios

### Base58 encode

#### empty input encodes to empty string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty input encodes to empty string
   - Expected: _enc_empty() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty input encodes to empty string")
expect(_enc_empty()).to_equal("")
```

</details>

#### single zero byte encodes to '1'

- single zero byte encodes to '1'
   - Expected: _enc_zero_one() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single zero byte encodes to '1'")
expect(_enc_zero_one()).to_equal("1")
```

</details>

#### three zero bytes encode to '111'

- three zero bytes encode to '111'
   - Expected: _enc_zero_three() equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("three zero bytes encode to '111'")
expect(_enc_zero_three()).to_equal("111")
```

</details>

#### [0x00, 0x00, 0x01] encodes to '112'

- [0x00, 0x00, 0x01] encodes to '112'
   - Expected: _enc_zero_zero_one() equals `112`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("[0x00, 0x00, 0x01] encodes to '112'")
expect(_enc_zero_zero_one()).to_equal("112")
```

</details>

#### [0x61] encodes to '2g'

- [0x61] encodes to '2g'
   - Expected: _enc_0x61() equals `2g`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("[0x61] encodes to '2g'")
expect(_enc_0x61()).to_equal("2g")
```

</details>

#### Hello World! encodes to '2NEpo7TZRRrLZSi2U'

- Hello World! encodes to '2NEpo7TZRRrLZSi2U'
   - Expected: _enc_hello_world() equals `2NEpo7TZRRrLZSi2U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Hello World! encodes to '2NEpo7TZRRrLZSi2U'")
expect(_enc_hello_world()).to_equal("2NEpo7TZRRrLZSi2U")
```

</details>

#### [32] (multiple of 32) encodes to 'Z', not empty

- [32] (multiple of 32) encodes to 'Z', not empty
   - Expected: _enc_multiple_of_32_a() equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("[32] (multiple of 32) encodes to 'Z', not empty")
expect(_enc_multiple_of_32_a()).to_equal("Z")
```

</details>

#### [64] (multiple of 32) encodes to '27', not empty

- [64] (multiple of 32) encodes to '27', not empty
   - Expected: _enc_multiple_of_32_b() equals `27`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("[64] (multiple of 32) encodes to '27', not empty")
expect(_enc_multiple_of_32_b()).to_equal("27")
```

</details>

### Base58 decode

#### empty string decodes to empty bytes

- empty string decodes to empty bytes
   - Expected: _dec_empty_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty string decodes to empty bytes")
expect(_dec_empty_ok()).to_equal(true)
```

</details>

#### '1' decodes to [0x00]

- '1' decodes to [0x00]
   - Expected: _dec_one_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("'1' decodes to [0x00]")
expect(_dec_one_ok()).to_equal(true)
```

</details>

#### '2g' decodes to [0x61]

- '2g' decodes to [0x61]
   - Expected: _dec_two_g() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("'2g' decodes to [0x61]")
expect(_dec_two_g()).to_equal(true)
```

</details>

#### excluded chars 0OIl return InvalidChar

- excluded chars 0OIl return InvalidChar
   - Expected: _dec_invalid_char_0() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("excluded chars 0OIl return InvalidChar")
expect(_dec_invalid_char_0()).to_equal(true)
```

</details>

### Base58Check

#### canonical P2PKH address encodes correctly

- canonical P2PKH address encodes correctly
   - Expected: _check_encode_p2pkh() equals `16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("canonical P2PKH address encodes correctly")
expect(_check_encode_p2pkh()).to_equal("16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM")
```

</details>

#### canonical P2PKH address decodes with version 0

- canonical P2PKH address decodes with version 0
   - Expected: _check_decode_p2pkh_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("canonical P2PKH address decodes with version 0")
expect(_check_decode_p2pkh_ok()).to_equal(true)
```

</details>

#### canonical P2PKH payload is 20 bytes

- canonical P2PKH payload is 20 bytes
   - Expected: _check_decode_p2pkh_payload_len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("canonical P2PKH payload is 20 bytes")
expect(_check_decode_p2pkh_payload_len()).to_equal(20)
```

</details>

#### mutated last char returns InvalidChecksum

- mutated last char returns InvalidChecksum
   - Expected: _check_decode_bad_checksum() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mutated last char returns InvalidChecksum")
expect(_check_decode_bad_checksum()).to_equal(true)
```

</details>

#### base58check round-trip is lossless

- base58check round-trip is lossless
   - Expected: _check_roundtrip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("base58check round-trip is lossless")
expect(_check_roundtrip()).to_equal(true)
```

</details>

#### base58check propagates InvalidChar from bad input

- base58check propagates InvalidChar from bad input
   - Expected: _check_invalid_char_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("base58check propagates InvalidChar from bad input")
expect(_check_invalid_char_error()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/base58_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Base58 encode, Base58 decode, Base58Check.
- Base58 encode
- Base58 decode
- Base58Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `fa065bf2a6e6b659a91368544d22c7015d688cc76cddcca2c61d9e7f94340d40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa065bf2a6e6b659a91368544d22c7015d688cc76cddcca2c61d9e7f94340d40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa065bf2a6e6b659a91368544d22c7015d688cc76cddcca2c61d9e7f94340d40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/encoding/base58_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/base58_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/base58_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/base58_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/base58_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/base58_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty input encodes to empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/base58_spec.spl:235:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single zero byte encodes to '1'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/base58_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'three zero bytes encode to '111'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
