# Argon2id Rfc9106 Kat Specification

> Tests covering Argon2id pure Simple smoke (small interpreter-tractable parameters), Argon2id determinism and input sensitivity, Argon2id RFC 9106 §5.3 — pending native fast path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argon2id Rfc9106 Kat Specification

## Scenarios

### Argon2id pure Simple smoke (small interpreter-tractable parameters)

#### returns 32 bytes for the default 32-byte tag length

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-SSPEC-UNIT
# Smallest valid memory: m_cost = 8 * parallelism = 8 KiB with p=1.
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag = argon2id(pwd, salt, 1, 8, 1, 32)
expect(tag.len()).to_equal(32)
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
val tag = argon2id(pwd, salt, 1, 8, 1, 16)
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
val tag = argon2id(pwd, salt, 1, 8, 1, 64)
expect(tag.len()).to_equal(64)
```

</details>

#### returns 96 bytes when tag_len=96 (multi-block H' branch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tag_len > 64 exercises the V_1..V_r||V_{r+1} long-output path of H'.
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag = argon2id(pwd, salt, 1, 8, 1, 96)
expect(tag.len()).to_equal(96)
```

</details>

### Argon2id determinism and input sensitivity

#### is deterministic — same inputs produce same tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = _ascii("password")
val salt = _ascii("somesalt")
val tag_a = argon2id(pwd, salt, 1, 8, 1, 32)
val tag_b = argon2id(pwd, salt, 1, 8, 1, 32)
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
val tag1 = argon2id(pwd, salt1, 1, 8, 1, 32)
val tag2 = argon2id(pwd, salt2, 1, 8, 1, 32)
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
val tag1 = argon2id(pwd1, salt, 1, 8, 1, 32)
val tag2 = argon2id(pwd2, salt, 1, 8, 1, 32)
expect(_bytes_to_hex(tag1)).to_not_equal(_bytes_to_hex(tag2))
```

</details>

### Argon2id RFC 9106 §5.3 — pending native fast path

#### RFC §5.3 (p=4, m=32 KiB, t=3, T=32) — pending FR argon2_native_runtime_helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reference RFC 9106 §5.3 inputs:
#   password = 32 bytes 0x01 ...
#   salt     = 16 bytes 0x02 ...
#   secret   = 8 bytes 0x03 ...
#   ad       = 12 bytes 0x04 ...
#   t=3, m=32, p=4, T=32, v=0x13
#   tag = 0c a4 fd 61 12 14 ...  (full 32 bytes per RFC §5.3)
# Memory-hard pure-Simple loop exceeds 60s watchdog under interpreter.
# Filed: doc/02_requirements/feature/argon2_native_runtime_helpers_2026-05-02.md
pending("argon2_native_runtime_helpers")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Argon2id pure Simple smoke (small interpreter-tractable parameters), Argon2id determinism and input sensitivity, Argon2id RFC 9106 §5.3 — pending native fast path.
- Argon2id pure Simple smoke (small interpreter-tractable parameters)
- Argon2id determinism and input sensitivity
- Argon2id RFC 9106 §5.3 — pending native fast path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `b9274126fb2d914b9bd15fba0a4c702e9db3ae5c32d80cd894994e9475d4c7fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b9274126fb2d914b9bd15fba0a4c702e9db3ae5c32d80cd894994e9475d4c7fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b9274126fb2d914b9bd15fba0a4c702e9db3ae5c32d80cd894994e9475d4c7fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **73/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/argon2id_rfc9106_kat_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=20
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=73; blocker cap makes effective=49
doc/06_spec/unit/lib/crypto/argon2id_rfc9106_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/argon2id_rfc9106_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:77:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 32 bytes for the default 32-byte tag length' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:86:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 16 bytes when tag_len=16' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:92:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 64 bytes when tag_len=64 (single-BLAKE2b-call H' branch)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/argon2id_rfc9106_kat_spec.spl:98:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns 96 bytes when tag_len=96 (multi-block H' branch)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
