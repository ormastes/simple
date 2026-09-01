# Tls Common Hooks Aes Gcm Specification

> Tests covering TLS common AES-GCM hooks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Common Hooks Aes Gcm Specification

## Scenarios

### TLS common AES-GCM hooks

#### encrypts NIST TC2 through pure Simple AES-GCM

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encrypts NIST TC2 through pure Simple AES-GCM
   - Expected: actual_hex equals `expected_hex`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts NIST TC2 through pure Simple AES-GCM")
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val plaintext_hex = "00000000000000000000000000000000"
val aad_hex = ""
val expected_hex = "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf"

val actual_hex = tls_hook_aes_gcm_encrypt_hex(key_hex, nonce_hex, plaintext_hex, aad_hex)

expect(actual_hex).to_equal(expected_hex)
```

</details>

#### decrypts NIST TC2 through pure Simple AES-GCM

- decrypts NIST TC2 through pure Simple AES-GCM
   - Expected: "decrypt should return plaintext" equals ``
   - Expected: actual_hex equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts NIST TC2 through pure Simple AES-GCM")
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val ciphertext_hex = "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf"
val aad_hex = ""

val actual_hex = tls_hook_aes_gcm_decrypt_hex(key_hex, nonce_hex, ciphertext_hex, aad_hex)

if actual_hex == nil:
    expect("decrypt should return plaintext").to_equal("")
else:
    expect(actual_hex).to_equal("00000000000000000000000000000000")
```

</details>

#### decrypts valid empty plaintext distinctly from authentication failure

- decrypts valid empty plaintext distinctly from authentication failure
   - Expected: "empty plaintext should not be nil" equals ``
   - Expected: actual_hex equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts valid empty plaintext distinctly from authentication failure")
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val ciphertext_hex = "58e2fccefa7e3061367f1d57a4e7455a"
val aad_hex = ""

val actual_hex = tls_hook_aes_gcm_decrypt_hex(key_hex, nonce_hex, ciphertext_hex, aad_hex)

if actual_hex == nil:
    expect("empty plaintext should not be nil").to_equal("")
else:
    expect(actual_hex).to_equal("")
```

</details>

#### rejects invalid tags without calling runtime AES-GCM externs

- rejects invalid tags without calling runtime AES-GCM externs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid tags without calling runtime AES-GCM externs")
val key_hex = "00000000000000000000000000000000"
val nonce_hex = "000000000000000000000000"
val ciphertext_hex = "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bd20"
val aad_hex = ""

val actual_hex = tls_hook_aes_gcm_decrypt_hex(key_hex, nonce_hex, ciphertext_hex, aad_hex)

expect(actual_hex).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS common AES-GCM hooks.
- TLS common AES-GCM hooks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `1a44b4d91a534cd06ea6c54e86597ed4e1ff1e562afc7b10eb1b77856213db38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a44b4d91a534cd06ea6c54e86597ed4e1ff1e562afc7b10eb1b77856213db38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a44b4d91a534cd06ea6c54e86597ed4e1ff1e562afc7b10eb1b77856213db38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl
mirror: doc/06_spec/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypts NIST TC2 through pure Simple AES-GCM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decrypts NIST TC2 through pure Simple AES-GCM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decrypts valid empty plaintext distinctly from authentication failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
