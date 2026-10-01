# kms_vendor_adapters_spec

> Purpose and audience: owning engineering team verifying KMS vendor transport adapters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kms_vendor_adapters_spec

Purpose and audience: owning engineering team verifying KMS vendor transport adapters.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/security/kms_vendor_adapters_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: owning engineering team verifying KMS vendor transport adapters.

## Scenarios

### KMS vendor transport adapters

#### builds AWS KMS Sign and Verify JSON RPC requests

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds AWS KMS Sign and Verify JSON RPC requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds AWS KMS Sign and Verify JSON RPC requests")
val sign = aws_kms_sign_request("https://kms.us-east-1.amazonaws.com", "arn:aws:kms:us-east-1:111122223333:key/key-1", "payload", "RSASSA_PSS_SHA_256", "AWS4-HMAC-SHA256 signed", 3000, "system")
val verify = aws_kms_verify_request("https://kms.us-east-1.amazonaws.com", "arn:aws:kms:us-east-1:111122223333:key/key-1", "payload", "sig", "RSASSA_PSS_SHA_256", "AWS4-HMAC-SHA256 signed", 3000, "system")

assert_equal(sign.method, "POST")
assert_equal(sign.headers["x-amz-target"], "TrentService.Sign")
assert_contains(sign.body, "RSASSA_PSS_SHA_256")
assert_equal(verify.method, "POST")
assert_equal(verify.headers["x-amz-target"], "TrentService.Verify")
assert_contains(verify.body, "sig")
```

</details>

#### contains AWS KMS SigV4 builders backed by opaque credential store

- contains AWS KMS SigV4 builders backed by opaque credential store


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains AWS KMS SigV4 builders backed by opaque credential store")
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")
val credential_source = file_read("src/lib/nogc_sync_mut/security/auth/credential_store.spl")

assert_contains(source, "aws_kms_sigv4_sign_request_from_credentials")
assert_contains(source, "aws_kms_sigv4_verify_request_from_credentials")
assert_contains(source, "aws_kms_sigv4_sign_request_from_temporary_credentials")
assert_contains(source, "x-amz-security-token")
assert_contains(source, "credential_store_aws_sigv4_authorization")
assert_contains(source, "credential_store_aws_sigv4_authorization_with_session_token")
assert_contains(credential_source, "fn credential_store_aws_sigv4_authorization")
assert_contains(credential_source, "fn credential_store_aws_sigv4_authorization_with_session_token")
assert_contains(credential_source, "sigv4_authorization_header")
```

</details>

#### contains AWS temporary credential signing with the session token header

- contains AWS temporary credential signing with the session token header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains AWS temporary credential signing with the session token header")
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")

assert_contains(source, "aws_kms_sigv4_sign_request_with_session_token")
assert_contains(source, "aws_kms_sigv4_headers_with_session_token")
assert_contains(source, "SigV4Header(name: \"x-amz-security-token\"")
assert_contains(source, "\"x-amz-security-token\": session_token")
```

</details>

#### contains bearer credential-backed builders for GCP Azure and HSM

- contains bearer credential-backed builders for GCP Azure and HSM


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains bearer credential-backed builders for GCP Azure and HSM")
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")
val credential_source = file_read("src/lib/nogc_sync_mut/security/auth/credential_store.spl")

assert_contains(source, "gcp_kms_asymmetric_sign_request_from_credentials")
assert_contains(source, "azure_key_vault_sign_request_from_credentials")
assert_contains(source, "azure_key_vault_verify_request_from_credentials")
assert_contains(source, "pkcs11_hsm_sign_request_from_credentials")
assert_contains(source, "pkcs11_hsm_verify_request_from_credentials")
assert_contains(source, "credential_store_bearer_authorization")
assert_contains(credential_source, "fn credential_store_bearer_authorization")
assert_equal(credential_source.contains("fn _credential_value"), false)
```

</details>

#### builds Google Cloud KMS asymmetricSign requests

- builds Google Cloud KMS asymmetricSign requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds Google Cloud KMS asymmetricSign requests")
val request = gcp_kms_asymmetric_sign_request("https://cloudkms.googleapis.com", "projects/p/locations/global/keyRings/r/cryptoKeys/k/cryptoKeyVersions/1", "sha256-digest", "oauth-token", 3000, "system")

assert_equal(request.method, "POST")
assert_contains(request.url, "asymmetricSign")
assert_equal(request.headers["authorization"], "Bearer oauth-token")
assert_contains(request.body, "sha256-digest")
```

</details>

#### builds Azure Key Vault sign and verify requests

- builds Azure Key Vault sign and verify requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds Azure Key Vault sign and verify requests")
val sign = azure_key_vault_sign_request("https://vault.vault.azure.net", "token-key/version-1", "digest-b64u", "PS256", "aad-token", 3000, "system")
val verify = azure_key_vault_verify_request("https://vault.vault.azure.net", "token-key/version-1", "digest-b64u", "sig-b64u", "PS256", "aad-token", 3000, "system")

assert_equal(sign.method, "POST")
assert_contains(sign.url, "sign")
assert_contains(sign.body, "PS256")
assert_equal(verify.method, "POST")
assert_contains(verify.url, "verify")
assert_contains(verify.body, "sig-b64u")
assert_equal(verify.headers["authorization"], "Bearer aad-token")
```

</details>

#### builds PKCS11 HSM gateway requests

- builds PKCS11 HSM gateway requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds PKCS11 HSM gateway requests")
val sign = pkcs11_hsm_sign_request("https://hsm.internal", "slot-0", "hsm://slot-0/key-1", "payload", "CKM_ECDSA_SHA256", "Bearer hsm-token", 3000, "mtls:hsm")
val verify = pkcs11_hsm_verify_request("https://hsm.internal", "slot-0", "hsm://slot-0/key-1", "payload", "sig", "CKM_ECDSA_SHA256", "Bearer hsm-token", 3000, "mtls:hsm")

assert_equal(sign.method, "POST")
assert_equal(sign.tls_profile, "mtls:hsm")
assert_contains(sign.body, "hsm://slot-0/key-1")
assert_equal(verify.method, "POST")
assert_contains(verify.body, "sig")
assert_equal(verify.headers["authorization"], "Bearer hsm-token")
```

</details>

#### does not include raw signing key fields

- does not include raw signing key fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not include raw signing key fields")
val request = aws_kms_sign_request("https://kms.us-east-1.amazonaws.com", "alias/simple-token", "payload", "RSASSA_PKCS1_V1_5_SHA_256", "", 3000, "system")

assert_equal(request.body.index_of("signing_key") < 0, true)
assert_equal(request.body.index_of("private_key") < 0, true)
assert_equal(request.body.index_of("secret") < 0, true)
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")
assert_equal(source.contains("GCP_ACCESS_TOKEN"), false)
assert_equal(source.contains("AZURE_ACCESS_TOKEN"), false)
```

</details>

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

- Canonical SPipe generation for source `5177e3a5ec1a193bfe415bf90c20a720bf45fe61df34c3906b05ae1c8a1383b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5177e3a5ec1a193bfe415bf90c20a720bf45fe61df34c3906b05ae1c8a1383b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5177e3a5ec1a193bfe415bf90c20a720bf45fe61df34c3906b05ae1c8a1383b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/security/kms_vendor_adapters_spec.spl
mirror: doc/06_spec/unit/lib/security/kms_vendor_adapters_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/security/kms_vendor_adapters_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/security/kms_vendor_adapters_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/security/kms_vendor_adapters_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds AWS KMS Sign and Verify JSON RPC requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/kms_vendor_adapters_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains AWS KMS SigV4 builders backed by opaque credential store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/kms_vendor_adapters_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains AWS temporary credential signing with the session token header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
