# Aws Sigv4 Specification

> Tests covering AWS SigV4 golden vector (AWS-published GET Object example).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aws Sigv4 Specification

## Scenarios

### AWS SigV4 golden vector (AWS-published GET Object example)

#### building blocks

#### hashes the empty string to the well-known SHA256(\

- hashes the empty string to the well-known SHA256(\
   - Expected: sigv4_sha256_hex("") equals `SIGV4_EMPTY_SHA256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes the empty string to the well-known SHA256(\")
expect(sigv4_sha256_hex("")).to_equal(SIGV4_EMPTY_SHA256)
```

</details>

#### builds the credential scope: date/region/service/aws4_request

- builds the credential scope: date/region/service/aws4_request
   - Expected: sigv4_credential_scope(VEC_DATE, VEC_REGION, VEC_SERVICE) equals `20130524/us-east-1/s3/aws4_request`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the credential scope: date/region/service/aws4_request")
expect(sigv4_credential_scope(VEC_DATE, VEC_REGION, VEC_SERVICE)).to_equal("20130524/us-east-1/s3/aws4_request")
```

</details>

#### hashes the AWS-published canonical request to the AWS-published hash

- hashes the AWS-published canonical request to the AWS-published hash
   - Expected: sigv4_sha256_hex(VEC_CANONICAL_REQUEST) equals `VEC_CANONICAL_REQUEST_HASH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes the AWS-published canonical request to the AWS-published hash")
expect(sigv4_sha256_hex(VEC_CANONICAL_REQUEST)).to_equal(VEC_CANONICAL_REQUEST_HASH)
```

</details>

#### builds the AWS-published string-to-sign from the canonical request

- builds the AWS-published string-to-sign from the canonical request
   - Expected: sigv4_string_to_sign(VEC_AMZ_DATE, scope, VEC_CANONICAL_REQUEST) equals `VEC_STRING_TO_SIGN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the AWS-published string-to-sign from the canonical request")
val scope = sigv4_credential_scope(VEC_DATE, VEC_REGION, VEC_SERVICE)
expect(sigv4_string_to_sign(VEC_AMZ_DATE, scope, VEC_CANONICAL_REQUEST)).to_equal(VEC_STRING_TO_SIGN)
```

</details>

#### computes the AWS-published final signature from the canonical request

- computes the AWS-published final signature from the canonical request
   - Expected: sig equals `VEC_SIGNATURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes the AWS-published final signature from the canonical request")
val sig = sigv4_compute_signature(VEC_SECRET_KEY, VEC_DATE, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, VEC_CANONICAL_REQUEST)
expect(sig).to_equal(VEC_SIGNATURE)
```

</details>

#### end-to-end presigned URL (locks canonical request + string-to-sign + signature together)

#### reproduces the exact AWS-published presigned GET URL

- reproduces the exact AWS-published presigned GET URL
   - Expected: url equals `VEC_PRESIGNED_URL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reproduces the exact AWS-published presigned GET URL")
val url = sigv4_presign_url("GET", VEC_ENDPOINT, VEC_HOST, "", "test.txt", VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, 86400)
expect(url).to_equal(VEC_PRESIGNED_URL)
```

</details>

#### sigv4_presign_get_url (adapter_minio's entry point) matches sigv4_presign_url(\

- sigv4_presign_get_url (adapter_minio's entry point) matches sigv4_presign_url(\
   - Expected: via_get equals `VEC_PRESIGNED_URL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sigv4_presign_get_url (adapter_minio's entry point) matches sigv4_presign_url(\")
val via_get = sigv4_presign_get_url(VEC_ENDPOINT, VEC_HOST, "", "test.txt", VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, 86400)
expect(via_get).to_equal(VEC_PRESIGNED_URL)
```

</details>

#### sigv4_presign_url(\

- sigv4_presign_url(\
   - Expected: put_url does not contain `X-Amz-Signature={VEC_SIGNATURE}`
   - Expected: put_url.starts_with("https://examplebucket.s3.amazonaws.com/test.txt?") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sigv4_presign_url(\")
val put_url = sigv4_presign_url("PUT", VEC_ENDPOINT, VEC_HOST, "", "test.txt", VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, 86400)
expect(put_url.contains("X-Amz-Signature={VEC_SIGNATURE}")).to_equal(false)
expect(put_url.starts_with("https://examplebucket.s3.amazonaws.com/test.txt?")).to_equal(true)
```

</details>

#### epoch_to_amz_datetime (used to build amz_datetime for every live call)

#### matches the vector's date for the epoch second AWS's example date corresponds to

- matches the vector's date for the epoch second AWS's example date corresponds to
   - Expected: epoch_to_amz_datetime(1369353600) equals `VEC_AMZ_DATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the vector's date for the epoch second AWS's example date corresponds to")
# 2013-05-24T00:00:00Z = 1369353600 (also asserted in adapter_minio_spec.spl)
expect(epoch_to_amz_datetime(1369353600)).to_equal(VEC_AMZ_DATE)
```

</details>

#### DELETE request, header-auth mode (self-derived golden vector — see comment above)

#### _build_object_path (adapter_minio's canonical-URI builder) produces the expected path-style URI

- _build_object_path (adapter_minio's canonical-URI builder) produces the expected path-style URI
   - Expected: _build_object_path(VEC_DELETE_BUCKET, VEC_DELETE_KEY) equals `VEC_DELETE_CANONICAL_URI`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("_build_object_path (adapter_minio's canonical-URI builder) produces the expected path-style URI")
expect(_build_object_path(VEC_DELETE_BUCKET, VEC_DELETE_KEY)).to_equal(VEC_DELETE_CANONICAL_URI)
```

</details>

#### sigv4_canonical_headers sorts host/x-amz-content-sha256/x-amz-date and builds the signed-headers list adapter_minio relies on

- sigv4_canonical_headers sorts host/x-amz-content-sha256/x-amz-date and builds the signed-headers list adapter_minio relies on
   - Expected: block equals `VEC_DELETE_HEADER_BLOCK`
   - Expected: signed equals `VEC_DELETE_SIGNED_HEADERS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sigv4_canonical_headers sorts host/x-amz-content-sha256/x-amz-date and builds the signed-headers list adapter_minio relies on")
var headers: [SigV4Header] = []
headers = headers + [SigV4Header(name: "host", value: VEC_HOST)]
headers = headers + [SigV4Header(name: "x-amz-content-sha256", value: SIGV4_EMPTY_SHA256)]
headers = headers + [SigV4Header(name: "x-amz-date", value: VEC_AMZ_DATE)]
val (block, signed) = sigv4_canonical_headers(headers)
expect(block).to_equal(VEC_DELETE_HEADER_BLOCK)
expect(signed).to_equal(VEC_DELETE_SIGNED_HEADERS)
```

</details>

#### hashes the self-derived DELETE canonical request to the independently-computed hash

- hashes the self-derived DELETE canonical request to the independently-computed hash
   - Expected: sigv4_sha256_hex(VEC_DELETE_CANONICAL_REQUEST) equals `VEC_DELETE_CANONICAL_REQUEST_HASH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes the self-derived DELETE canonical request to the independently-computed hash")
expect(sigv4_sha256_hex(VEC_DELETE_CANONICAL_REQUEST)).to_equal(VEC_DELETE_CANONICAL_REQUEST_HASH)
```

</details>

#### computes the independently-derived final signature from the DELETE canonical request

- computes the independently-derived final signature from the DELETE canonical request
   - Expected: sig equals `VEC_DELETE_SIGNATURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes the independently-derived final signature from the DELETE canonical request")
val sig = sigv4_compute_signature(VEC_SECRET_KEY, VEC_DATE, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, VEC_DELETE_CANONICAL_REQUEST)
expect(sig).to_equal(VEC_DELETE_SIGNATURE)
```

</details>

#### sigv4_authorization_header (adapter_minio.minio_delete_object's exact entry point) reproduces the full Authorization header

- sigv4_authorization_header (adapter_minio.minio_delete_object's exact entry point) reproduces the full Authorization header
   - Expected: auth equals `VEC_DELETE_AUTH_HEADER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sigv4_authorization_header (adapter_minio.minio_delete_object's exact entry point) reproduces the full Authorization header")
var headers: [SigV4Header] = []
headers = headers + [SigV4Header(name: "host", value: VEC_HOST)]
headers = headers + [SigV4Header(name: "x-amz-content-sha256", value: SIGV4_EMPTY_SHA256)]
headers = headers + [SigV4Header(name: "x-amz-date", value: VEC_AMZ_DATE)]
val auth = sigv4_authorization_header(
    "DELETE", VEC_DELETE_CANONICAL_URI, "", headers, SIGV4_EMPTY_SHA256,
    VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE
)
expect(auth).to_equal(VEC_DELETE_AUTH_HEADER)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/aws_sigv4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AWS SigV4 golden vector (AWS-published GET Object example).
- AWS SigV4 golden vector (AWS-published GET Object example)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `9921e0055ef5552559d1db7c58a263bfb76a4fa32f163815bbaec6c940914bef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9921e0055ef5552559d1db7c58a263bfb76a4fa32f163815bbaec6c940914bef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9921e0055ef5552559d1db7c58a263bfb76a4fa32f163815bbaec6c940914bef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/devhub/aws_sigv4_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/aws_sigv4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/aws_sigv4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/aws_sigv4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/aws_sigv4_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes the empty string to the well-known SHA256(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/aws_sigv4_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the credential scope: date/region/service/aws4_request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/aws_sigv4_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes the AWS-published canonical request to the AWS-published hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
