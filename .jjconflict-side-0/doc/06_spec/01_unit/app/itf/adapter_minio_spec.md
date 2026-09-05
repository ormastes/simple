# Adapter Minio Specification

> <details>

<!-- sdn-diagram:id=adapter_minio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_minio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_minio_spec -> std
adapter_minio_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_minio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Minio Specification

## Scenarios

### MinIO adapter

#### config parsing

#### parses [minio] flat-section SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "[bitbucket]\nurl = x\n[minio]\nurl = https://minio.corp:9000\nregion = us-east-1\naccess_key = AKIA--\nsecret_key = SECRET\ntls_skip_verify = false\n"
val cfg = _parse_minio_section(sdn)
expect(cfg.url).to_equal("https://minio.corp:9000")
expect(cfg.region).to_equal("us-east-1")
expect(cfg.access_key).to_equal("AKIA--")
expect(cfg.secret_key).to_equal("SECRET")
expect(cfg.tls_skip_verify).to_equal(false)
```

</details>

#### honors tls_skip_verify=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "[minio]\nurl = https://x\naccess_key = a\nsecret_key = s\ntls_skip_verify = true\n"
val cfg = _parse_minio_section(sdn)
expect(cfg.tls_skip_verify).to_equal(true)
```

</details>

#### ListBuckets XML

#### extracts every <Bucket> with Name + CreationDate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buckets = _parse_list_buckets_xml(LIST_BUCKETS_XML)
expect(buckets.len()).to_equal(2)
expect(buckets[0].name).to_equal("firmware-images")
expect(buckets[0].creation_date).to_equal("2025-01-10T08:00:00.000Z")
expect(buckets[1].name).to_equal("logs")
```

</details>

#### returns empty list for body with no <Buckets> block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = _parse_list_buckets_xml("<Other/>")
expect(out.len()).to_equal(0)
```

</details>

#### ListObjectsV2 XML

#### extracts Contents[] with Key + Size + LastModified

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _parse_list_objects_xml(LIST_OBJECTS_XML_TRUNC)
expect(r.objects.len()).to_equal(2)
expect(r.objects[0].key).to_equal("zynq/v1/fw.bin")
expect(r.objects[0].size).to_equal(1048576)
expect(r.objects[1].key).to_equal("zynq/v2/fw.bin")
expect(r.objects[1].size).to_equal(134217728)
```

</details>

#### captures IsTruncated + NextContinuationToken for pagination

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _parse_list_objects_xml(LIST_OBJECTS_XML_TRUNC)
expect(r.is_truncated).to_equal(true)
expect(r.next_continuation_token).to_equal("TOKEN_ABC")
```

</details>

#### marks final page as not truncated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = _parse_list_objects_xml(LIST_OBJECTS_XML_FINAL)
expect(r.is_truncated).to_equal(false)
expect(r.objects.len()).to_equal(1)
```

</details>

#### error mapping

#### 200 maps to ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = map_s3_error(200, "<ok/>", "")
expect(m.kind).to_equal("ok")
```

</details>

#### 403 with <Error><Code>AccessDenied</Code> maps to auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = map_s3_error(403, ERR_403, "")
expect(m.kind).to_equal("auth")
expect(m.message.contains("AccessDenied")).to_equal(true)
expect(m.message.contains("Access Denied")).to_equal(true)
```

</details>

#### 404 with NoSuchKey maps to not_found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = map_s3_error(404, ERR_404, "")
expect(m.kind).to_equal("not_found")
expect(m.message.contains("NoSuchKey")).to_equal(true)
```

</details>

#### 503 maps to unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = map_s3_error(503, ERR_503, "")
expect(m.kind).to_equal("unavailable")
expect(m.message.contains("ServiceUnavailable")).to_equal(true)
```

</details>

#### transport error maps to network

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = map_s3_error(0, "", "connection refused")
expect(m.kind).to_equal("network")
expect(m.message).to_equal("connection refused")
```

</details>

#### 409 maps to conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = map_s3_error(409, "<Error><Code>BucketAlreadyExists</Code><Message>x</Message></Error>", "")
expect(m.kind).to_equal("conflict")
```

</details>

#### presigned URL

#### produces a path-style URL with X-Amz-Signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = MinioConfig(url: "https://minio.corp:9000", region: "us-east-1", access_key: "AKIA--", secret_key: "SECRET", tls_skip_verify: false)
val (ok, url, _err) = minio_presign_get(cfg, "firmware-images", "zynq/v1/fw.bin", 3600)
expect(ok).to_equal(true)
expect(url.starts_with("https://minio.corp:9000/firmware-images/zynq/v1/fw.bin?")).to_equal(true)
expect(url.contains("X-Amz-Signature=")).to_equal(true)
expect(url.contains("X-Amz-Algorithm=AWS4-HMAC-SHA256")).to_equal(true)
```

</details>

#### rejects expires > 604800 (7 days)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = MinioConfig(url: "https://x", region: "us-east-1", access_key: "a", secret_key: "s", tls_skip_verify: false)
val (ok, _u, err) = minio_presign_get(cfg, "b", "k", 700000)
expect(ok).to_equal(false)
expect(err.contains("604800")).to_equal(true)
```

</details>

#### epoch_to_amz_datetime

#### formats epoch 0 as 19700101T000000Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(epoch_to_amz_datetime(0)).to_equal("19700101T000000Z")
```

</details>

#### formats vector epoch 1369353600 as 20130524T000000Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2013-05-24 00:00:00 UTC = 1369353600
expect(epoch_to_amz_datetime(1369353600)).to_equal("20130524T000000Z")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_minio_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MinIO adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
