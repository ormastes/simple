# Argon2d Kat Specification

> Tests covering Argon2d pure Simple smoke (small interpreter-tractable parameters), Argon2d determinism and input sensitivity, Argon2d RFC 9106 5.1 -- pending native fast path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argon2d Kat Specification

## Scenarios

### Argon2d pure Simple smoke (small interpreter-tractable parameters)

#### returns 32 bytes for the default 32-byte tag length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### returns 16 bytes when tag_len=16

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag = argon2d(pwd, salt, 1, 8, 1, 16)
expect(tag.len()).to_equal(16)
```

</details>

#### returns 64 bytes when tag_len=64 (single-BLAKE2b-call H' branch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag = argon2d(pwd, salt, 1, 8, 1, 64)
expect(tag.len()).to_equal(64)
```

</details>

#### returns 96 bytes when tag_len=96 (multi-block H' branch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag = argon2d(pwd, salt, 1, 8, 1, 96)
expect(tag.len()).to_equal(96)
```

</details>

### Argon2d determinism and input sensitivity

#### is deterministic -- same inputs produce same tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag_a = argon2d(pwd, salt, 1, 8, 1, 32)
val tag_b = argon2d(pwd, salt, 1, 8, 1, 32)
expect(_bytes_to_hex(tag_a)).to_equal(_bytes_to_hex(tag_b))
```

</details>

#### differing salt produces different tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt1 = _ascii("somesalt")
val salt2 = _ascii("othersalt")
val tag1 = argon2d(pwd, salt1, 1, 8, 1, 32)
val tag2 = argon2d(pwd, salt2, 1, 8, 1, 32)
expect(_bytes_to_hex(tag1)).to_not_equal(_bytes_to_hex(tag2))
```

</details>

#### differing password produces different tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = _ascii("somesalt")
val pwd1 = _ascii("password")
val pwd2 = _ascii("Password")
val tag1 = argon2d(pwd1, salt, 1, 8, 1, 32)
val tag2 = argon2d(pwd2, salt, 1, 8, 1, 32)
expect(_bytes_to_hex(tag1)).to_not_equal(_bytes_to_hex(tag2))
```

</details>

#### non-empty key changes output vs empty key (argon2d_hash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val empty: [u8] = []
val key = _repeat_bytes(1, 4)
val tag_no_key = argon2d_hash(pwd, salt, 1, 8, 1, empty, empty, 32)
val tag_with_key = argon2d_hash(pwd, salt, 1, 8, 1, key, empty, 32)
expect(_bytes_to_hex(tag_no_key)).to_not_equal(_bytes_to_hex(tag_with_key))
```

</details>

#### non-empty ad changes output vs empty ad (argon2d_hash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val empty: [u8] = []
val ad = _repeat_bytes(4, 4)
val tag_no_ad = argon2d_hash(pwd, salt, 1, 8, 1, empty, empty, 32)
val tag_with_ad = argon2d_hash(pwd, salt, 1, 8, 1, empty, ad, 32)
expect(_bytes_to_hex(tag_no_ad)).to_not_equal(_bytes_to_hex(tag_with_ad))
```

</details>

### Argon2d RFC 9106 5.1 -- pending native fast path

#### RFC 5.1 (p=4, m=32 KiB, t=3, T=32) -- pending FR argon2_native_runtime_helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 9106 5.1 inputs:
#   password = 32 bytes 0x01, salt = 16 bytes 0x02
#   secret = 8 bytes 0x03, ad = 12 bytes 0x04
#   t=3, m=32, p=4, T=32, v=0x13
#   tag = 51 2b 39 1b 6f 11 62 97 53 71 d3 09 19 73 42 94
#         f8 68 e3 be 39 84 f3 c1 a1 3a 4d b9 fa be 4a cb
# Memory-hard pure-Simple loop exceeds 60s watchdog under interpreter.
# Filed: doc/02_requirements/feature/argon2_native_runtime_helpers_2026-05-02.md
pending("argon2_native_runtime_helpers")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/argon2d_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Argon2d pure Simple smoke (small interpreter-tractable parameters), Argon2d determinism and input sensitivity, Argon2d RFC 9106 5.1 -- pending native fast path.
- Argon2d pure Simple smoke (small interpreter-tractable parameters)
- Argon2d determinism and input sensitivity
- Argon2d RFC 9106 5.1 -- pending native fast path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `21ca66f1ffedebe837b708f341b72e2719e388b653e7bf0c176b50bde5f69cee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21ca66f1ffedebe837b708f341b72e2719e388b653e7bf0c176b50bde5f69cee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21ca66f1ffedebe837b708f341b72e2719e388b653e7bf0c176b50bde5f69cee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **73/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/crypto/argon2d_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/argon2d_kat_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=20
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=73; blocker cap makes effective=49
doc/06_spec/unit/os/crypto/argon2d_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/argon2d_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/argon2d_kat_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/os/crypto/argon2d_kat_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/os/crypto/argon2d_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/argon2d_kat_spec.spl:66:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 32 bytes for the default 32-byte tag length' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/crypto/argon2d_kat_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 16 bytes when tag_len=16' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/crypto/argon2d_kat_spec.spl:80:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 64 bytes when tag_len=64 (single-BLAKE2b-call H' branch)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/crypto/argon2d_kat_spec.spl:86:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 96 bytes when tag_len=96 (multi-block H' branch)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
