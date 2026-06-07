# Kms Vendor Adapters Specification

> <details>

<!-- sdn-diagram:id=kms_vendor_adapters_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kms_vendor_adapters_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kms_vendor_adapters_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kms_vendor_adapters_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kms Vendor Adapters Specification

## Scenarios

### KMS vendor transport adapters

#### builds AWS KMS Sign and Verify JSON RPC requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl")

expect(source).to_contain("aws_kms_sigv4_sign_request_with_session_token")
expect(source).to_contain("aws_kms_sigv4_headers_with_session_token")
expect(source).to_contain("SigV4Header(name: \"x-amz-security-token\"")
expect(source).to_contain("\"x-amz-security-token\": session_token")
```

</details>

#### contains bearer credential-backed builders for GCP Azure and HSM

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = gcp_kms_asymmetric_sign_request("https://cloudkms.googleapis.com", "projects/p/locations/global/keyRings/r/cryptoKeys/k/cryptoKeyVersions/1", "sha256-digest", "oauth-token", 3000, "system")

expect(request.method).to_equal("POST")
expect(request.url).to_contain("asymmetricSign")
expect(request.headers["authorization"]).to_equal("Bearer oauth-token")
expect(request.body).to_contain("sha256-digest")
```

</details>

#### builds Azure Key Vault sign and verify requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
