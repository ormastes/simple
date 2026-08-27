# Kms Vendor Adapters Specification

> Tests covering KMS vendor transport adapters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kms Vendor Adapters Specification

## Scenarios

### KMS vendor transport adapters

#### builds AWS KMS Sign and Verify JSON RPC requests

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds AWS KMS Sign and Verify JSON RPC requests
   - Expected: sign.method equals `POST`
   - Expected: sign.headers["x-amz-target"] equals `TrentService.Sign`
   - Expected: verify.method equals `POST`
   - Expected: verify.headers["x-amz-target"] equals `TrentService.Verify`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds AWS KMS Sign and Verify JSON RPC requests")
val sign = aws_kms_sign_request("https://kms.us-east-1.amazonaws.com", "arn:aws:kms:us-east-1:111122223333:key/key-1", "payload", "RSASSA_PSS_SHA_256", "AWS4-HMAC-SHA256 signed", 3000, "system")
val verify = aws_kms_verify_request("https://kms.us-east-1.amazonaws.com", "arn:aws:kms:us-east-1:111122223333:key/key-1", "payload", "sig", "RSASSA_PSS_SHA_256", "AWS4-HMAC-SHA256 signed", 3000, "system")

expect(sign.method).to_equal("POST")
expect(sign.headers["x-amz-target"]).to_equal("TrentService.Sign")
expect(sign.body).to_contain("RSASSA_PSS_SHA_256")
expect(verify.method).to_equal("POST")
expect(verify.headers["x-amz-target"]).to_equal("TrentService.Verify")
expect(verify.body).to_contain("sig")
```

</details>

#### contains AWS KMS SigV4 builders backed by opaque credential store

- contains AWS KMS SigV4 builders backed by opaque credential store


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains AWS KMS SigV4 builders backed by opaque credential store")
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")
val credential_source = file_read("src/lib/nogc_sync_mut/security/auth/credential_store.spl")

expect(source).to_contain("aws_kms_sigv4_sign_request_from_credentials")
expect(source).to_contain("aws_kms_sigv4_verify_request_from_credentials")
expect(source).to_contain("aws_kms_sigv4_sign_request_from_temporary_credentials")
expect(source).to_contain("x-amz-security-token")
expect(source).to_contain("credential_store_aws_sigv4_authorization")
expect(source).to_contain("credential_store_aws_sigv4_authorization_with_session_token")
expect(credential_source).to_contain("fn credential_store_aws_sigv4_authorization")
expect(credential_source).to_contain("fn credential_store_aws_sigv4_authorization_with_session_token")
expect(credential_source).to_contain("sigv4_authorization_header")
```

</details>

#### contains AWS temporary credential signing with the session token header

- contains AWS temporary credential signing with the session token header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains AWS temporary credential signing with the session token header")
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")

expect(source).to_contain("aws_kms_sigv4_sign_request_with_session_token")
expect(source).to_contain("aws_kms_sigv4_headers_with_session_token")
expect(source).to_contain("SigV4Header(name: \"x-amz-security-token\"")
expect(source).to_contain("\"x-amz-security-token\": session_token")
```

</details>

#### contains bearer credential-backed builders for GCP Azure and HSM

- contains bearer credential-backed builders for GCP Azure and HSM
   - Expected: credential_source does not contain `fn _credential_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains bearer credential-backed builders for GCP Azure and HSM")
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")
val credential_source = file_read("src/lib/nogc_sync_mut/security/auth/credential_store.spl")

expect(source).to_contain("gcp_kms_asymmetric_sign_request_from_credentials")
expect(source).to_contain("azure_key_vault_sign_request_from_credentials")
expect(source).to_contain("azure_key_vault_verify_request_from_credentials")
expect(source).to_contain("pkcs11_hsm_sign_request_from_credentials")
expect(source).to_contain("pkcs11_hsm_verify_request_from_credentials")
expect(source).to_contain("credential_store_bearer_authorization")
expect(credential_source).to_contain("fn credential_store_bearer_authorization")
expect(credential_source.contains("fn _credential_value")).to_equal(false)
```

</details>

#### builds Google Cloud KMS asymmetricSign requests

- builds Google Cloud KMS asymmetricSign requests
   - Expected: request.method equals `POST`
   - Expected: request.headers["authorization"] equals `Bearer oauth-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds Google Cloud KMS asymmetricSign requests")
val request = gcp_kms_asymmetric_sign_request("https://cloudkms.googleapis.com", "projects/p/locations/global/keyRings/r/cryptoKeys/k/cryptoKeyVersions/1", "sha256-digest", "oauth-token", 3000, "system")

expect(request.method).to_equal("POST")
expect(request.url).to_contain("asymmetricSign")
expect(request.headers["authorization"]).to_equal("Bearer oauth-token")
expect(request.body).to_contain("sha256-digest")
```

</details>

#### builds Azure Key Vault sign and verify requests

- builds Azure Key Vault sign and verify requests
   - Expected: sign.method equals `POST`
   - Expected: verify.method equals `POST`
   - Expected: verify.headers["authorization"] equals `Bearer aad-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds Azure Key Vault sign and verify requests")
val sign = azure_key_vault_sign_request("https://vault.vault.azure.net", "token-key/version-1", "digest-b64u", "PS256", "aad-token", 3000, "system")
val verify = azure_key_vault_verify_request("https://vault.vault.azure.net", "token-key/version-1", "digest-b64u", "sig-b64u", "PS256", "aad-token", 3000, "system")

expect(sign.method).to_equal("POST")
expect(sign.url).to_contain("sign")
expect(sign.body).to_contain("PS256")
expect(verify.method).to_equal("POST")
expect(verify.url).to_contain("verify")
expect(verify.body).to_contain("sig-b64u")
expect(verify.headers["authorization"]).to_equal("Bearer aad-token")
```

</details>

#### builds PKCS11 HSM gateway requests

- builds PKCS11 HSM gateway requests
   - Expected: sign.method equals `POST`
   - Expected: sign.tls_profile equals `mtls:hsm`
   - Expected: verify.method equals `POST`
   - Expected: verify.headers["authorization"] equals `Bearer hsm-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds PKCS11 HSM gateway requests")
val sign = pkcs11_hsm_sign_request("https://hsm.internal", "slot-0", "hsm://slot-0/key-1", "payload", "CKM_ECDSA_SHA256", "Bearer hsm-token", 3000, "mtls:hsm")
val verify = pkcs11_hsm_verify_request("https://hsm.internal", "slot-0", "hsm://slot-0/key-1", "payload", "sig", "CKM_ECDSA_SHA256", "Bearer hsm-token", 3000, "mtls:hsm")

expect(sign.method).to_equal("POST")
expect(sign.tls_profile).to_equal("mtls:hsm")
expect(sign.body).to_contain("hsm://slot-0/key-1")
expect(verify.method).to_equal("POST")
expect(verify.body).to_contain("sig")
expect(verify.headers["authorization"]).to_equal("Bearer hsm-token")
```

</details>

#### does not include raw signing key fields

- does not include raw signing key fields
   - Expected: request.body.index_of("signing_key") < 0 is true
   - Expected: request.body.index_of("private_key") < 0 is true
   - Expected: request.body.index_of("secret") < 0 is true
   - Expected: source does not contain `GCP_ACCESS_TOKEN`
   - Expected: source does not contain `AZURE_ACCESS_TOKEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not include raw signing key fields")
val request = aws_kms_sign_request("https://kms.us-east-1.amazonaws.com", "alias/simple-token", "payload", "RSASSA_PKCS1_V1_5_SHA_256", "", 3000, "system")

expect(request.body.index_of("signing_key") < 0).to_equal(true)
expect(request.body.index_of("private_key") < 0).to_equal(true)
expect(request.body.index_of("secret") < 0).to_equal(true)
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")
expect(source.contains("GCP_ACCESS_TOKEN")).to_equal(false)
expect(source.contains("AZURE_ACCESS_TOKEN")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security/kms_vendor_adapters_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering KMS vendor transport adapters.
- KMS vendor transport adapters

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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3a6a75feb4015687113f28922665a55363caef1010e852ab0711b42de623fad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3a6a75feb4015687113f28922665a55363caef1010e852ab0711b42de623fad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3a6a75feb4015687113f28922665a55363caef1010e852ab0711b42de623fad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/security/kms_vendor_adapters_spec.spl
mirror: doc/06_spec/01_unit/lib/security/kms_vendor_adapters_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/security/kms_vendor_adapters_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/security/kms_vendor_adapters_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/security/kms_vendor_adapters_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/security/kms_vendor_adapters_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/security/kms_vendor_adapters_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds AWS KMS Sign and Verify JSON RPC requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/security/kms_vendor_adapters_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains AWS KMS SigV4 builders backed by opaque credential store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/security/kms_vendor_adapters_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains AWS temporary credential signing with the session token header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
