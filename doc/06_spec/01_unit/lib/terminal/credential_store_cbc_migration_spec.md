# Credential Store Cbc Migration Specification

> Tests covering credential store — random-IV AES-256-CBC (v2), credential store — v1 legacy records remain readable (migration).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Credential Store Cbc Migration Specification

## Scenarios

### credential store — random-IV AES-256-CBC (v2)

#### writes records carrying the v2 version marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes records carrying the v2 version marker
   - Expected: _ensure_key() is true
   - Expected: enc.starts_with("encrypted:v2:") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes records carrying the v2 version marker")
expect(_ensure_key()).to_equal(true)
val enc = credential_encrypt("hunter2", _key_path())
expect(enc.starts_with("encrypted:v2:")).to_equal(true)
```

</details>

#### round-trips a credential through encrypt/decrypt

- round-trips a credential through encrypt/decrypt
   - Expected: _ensure_key() is true
   - Expected: credential_decrypt(enc, _key_path()) equals `correct horse battery staple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a credential through encrypt/decrypt")
expect(_ensure_key()).to_equal(true)
val enc = credential_encrypt("correct horse battery staple", _key_path())
expect(credential_decrypt(enc, _key_path())).to_equal("correct horse battery staple")
```

</details>

#### produces DIFFERENT ciphertext for the SAME plaintext (IV is random)

- produces DIFFERENT ciphertext for the SAME plaintext (IV is random)
   - Expected: _ensure_key() is true
   - Expected: a == b is false
   - Expected: credential_decrypt(a, _key_path()) equals `same_secret_value`
   - Expected: credential_decrypt(b, _key_path()) equals `same_secret_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces DIFFERENT ciphertext for the SAME plaintext (IV is random)")
# This is the security-critical assertion. Under the old deterministic
# plaintext-derived IV these two strings were byte-identical.
expect(_ensure_key()).to_equal(true)
val a = credential_encrypt("same_secret_value", _key_path())
val b = credential_encrypt("same_secret_value", _key_path())
expect(a == b).to_equal(false)
expect(credential_decrypt(a, _key_path())).to_equal("same_secret_value")
expect(credential_decrypt(b, _key_path())).to_equal("same_secret_value")
```

</details>

#### round-trips a long multi-block credential

- round-trips a long multi-block credential
   - Expected: _ensure_key() is true
   - Expected: credential_decrypt(enc, _key_path()) equals `secret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a long multi-block credential")
expect(_ensure_key()).to_equal(true)
val secret = "0123456789abcdef0123456789abcdef0123456789abcdefEXTRA"
val enc = credential_encrypt(secret, _key_path())
expect(credential_decrypt(enc, _key_path())).to_equal(secret)
```

</details>

#### still reports v2 records as encrypted

- still reports v2 records as encrypted
   - Expected: _ensure_key() is true
   - Expected: credential_is_encrypted(credential_encrypt("x", _key_path())) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports v2 records as encrypted")
expect(_ensure_key()).to_equal(true)
expect(credential_is_encrypted(credential_encrypt("x", _key_path()))).to_equal(true)
```

</details>

### credential store — v1 legacy records remain readable (migration)

#### decrypts a pre-2026-08-08 CTR record that has no version marker

- decrypts a pre-2026-08-08 CTR record that has no version marker
   - Expected: _ensure_key() is true
   - Expected: legacy.starts_with("encrypted:v2:") is false
   - Expected: credential_decrypt(legacy, _key_path()) equals `legacy_password`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts a pre-2026-08-08 CTR record that has no version marker")
expect(_ensure_key()).to_equal(true)
val legacy = _legacy_v1_record("legacy_password")
expect(legacy.starts_with("encrypted:v2:")).to_equal(false)
expect(credential_decrypt(legacy, _key_path())).to_equal("legacy_password")
```

</details>

#### decrypts a legacy record whose length is not a multiple of 16

- decrypts a legacy record whose length is not a multiple of 16
   - Expected: _ensure_key() is true
   - Expected: credential_decrypt(legacy, _key_path()) equals `seven17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts a legacy record whose length is not a multiple of 16")
# CTR preserved length, so v1 ciphertexts are frequently unaligned —
# feeding one to the new CBC decryptor would return nothing.
expect(_ensure_key()).to_equal(true)
val legacy = _legacy_v1_record("seven17")
expect(credential_decrypt(legacy, _key_path())).to_equal("seven17")
```

</details>

#### rejects a value with no encrypted: prefix

- rejects a value with no encrypted: prefix
   - Expected: credential_decrypt("plain_text_value", _key_path()) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a value with no encrypted: prefix")
expect(credential_decrypt("plain_text_value", _key_path())).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/terminal/credential_store_cbc_migration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering credential store — random-IV AES-256-CBC (v2), credential store — v1 legacy records remain readable (migration).
- credential store — random-IV AES-256-CBC (v2)
- credential store — v1 legacy records remain readable (migration)

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

- Canonical SPipe generation for source `e66131b1d601139950a497364f9a594e9addd43b4bf87596855016468886cda2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e66131b1d601139950a497364f9a594e9addd43b4bf87596855016468886cda2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e66131b1d601139950a497364f9a594e9addd43b4bf87596855016468886cda2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/terminal/credential_store_cbc_migration_spec.spl
mirror: doc/06_spec/01_unit/lib/terminal/credential_store_cbc_migration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/terminal/credential_store_cbc_migration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/terminal/credential_store_cbc_migration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/terminal/credential_store_cbc_migration_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes records carrying the v2 version marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/terminal/credential_store_cbc_migration_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a credential through encrypt/decrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/terminal/credential_store_cbc_migration_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces DIFFERENT ciphertext for the SAME plaintext (IV is random)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
