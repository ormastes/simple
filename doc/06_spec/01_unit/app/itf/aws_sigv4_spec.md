# Aws Sigv4 Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aws Sigv4 Specification

## Scenarios

### AWS SigV4 golden vector (AWS-published GET Object example)

#### building blocks

#### hashes the empty string to the well-known SHA256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sigv4_sha256_hex("")).to_equal(SIGV4_EMPTY_SHA256)
```

</details>

#### builds the credential scope: date/region/service/aws4_request

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sigv4_credential_scope(VEC_DATE, VEC_REGION, VEC_SERVICE)).to_equal("20130524/us-east-1/s3/aws4_request")
```

</details>

#### hashes the AWS-published canonical request to the AWS-published hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sigv4_sha256_hex(VEC_CANONICAL_REQUEST)).to_equal(VEC_CANONICAL_REQUEST_HASH)
```

</details>

#### builds the AWS-published string-to-sign from the canonical request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = sigv4_credential_scope(VEC_DATE, VEC_REGION, VEC_SERVICE)
expect(sigv4_string_to_sign(VEC_AMZ_DATE, scope, VEC_CANONICAL_REQUEST)).to_equal(VEC_STRING_TO_SIGN)
```

</details>

#### computes the AWS-published final signature from the canonical request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = sigv4_compute_signature(VEC_SECRET_KEY, VEC_DATE, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, VEC_CANONICAL_REQUEST)
expect(sig).to_equal(VEC_SIGNATURE)
```

</details>

#### end-to-end presigned URL (locks canonical request + string-to-sign + signature together)

#### reproduces the exact AWS-published presigned GET URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = sigv4_presign_url("GET", VEC_ENDPOINT, VEC_HOST, "", "test.txt", VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, 86400)
expect(url).to_equal(VEC_PRESIGNED_URL)
```

</details>

#### sigv4_presign_get_url (adapter_minio's entry point) matches sigv4_presign_url(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val via_get = sigv4_presign_get_url(VEC_ENDPOINT, VEC_HOST, "", "test.txt", VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, 86400)
expect(via_get).to_equal(VEC_PRESIGNED_URL)
```

</details>

#### sigv4_presign_url(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val put_url = sigv4_presign_url("PUT", VEC_ENDPOINT, VEC_HOST, "", "test.txt", VEC_ACCESS_KEY, VEC_SECRET_KEY, VEC_REGION, VEC_SERVICE, VEC_AMZ_DATE, 86400)
expect(put_url.contains("X-Amz-Signature={VEC_SIGNATURE}")).to_equal(false)
expect(put_url.starts_with("https://examplebucket.s3.amazonaws.com/test.txt?")).to_equal(true)
```

</details>

#### epoch_to_amz_datetime (used to build amz_datetime for every live call)

#### matches the vector's date for the epoch second AWS's example date corresponds to

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2013-05-24T00:00:00Z = 1369353600 (also asserted in adapter_minio_spec.spl)
expect(epoch_to_amz_datetime(1369353600)).to_equal(VEC_AMZ_DATE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/aws_sigv4_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AWS SigV4 golden vector (AWS-published GET Object example)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
