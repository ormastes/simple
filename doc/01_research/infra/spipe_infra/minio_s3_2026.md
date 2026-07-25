# MinIO / S3-Compatible Client API Research (April 2026)

Target: `src/app/itf/adapter_minio.spl` — pure-Simple, no SDK, raw HTTP + AWS Signature V4.

---

## 1. Endpoint Reference

MinIO speaks the S3 wire protocol verbatim. All examples use **path-style addressing**
(`https://HOST:PORT/{bucket}/{key}`) because on-prem MinIO deployments typically cannot do
virtual-host style without custom DNS.

Sources:
- https://docs.aws.amazon.com/AmazonS3/latest/API/API_ListBuckets.html
- https://docs.aws.amazon.com/AmazonS3/latest/API/API_ListObjectsV2.html
- https://docs.aws.amazon.com/AmazonS3/latest/API/API_GetObject.html
- https://docs.aws.amazon.com/AmazonS3/latest/API/API_HeadObject.html
- https://docs.aws.amazon.com/AmazonS3/latest/API/API_PutObject.html
- https://docs.aws.amazon.com/AmazonS3/latest/API/sigv4-query-string-auth.html

### 1.1 ListBuckets — `GET /`

```
GET / HTTP/1.1
Host: minio.corp:9000
x-amz-date: 20260426T120000Z
x-amz-content-sha256: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
Authorization: AWS4-HMAC-SHA256 Credential=...
```

Response XML (200 OK):
```xml
<ListAllMyBucketsResult>
  <Owner><ID>...</ID><DisplayName>...</DisplayName></Owner>
  <Buckets>
    <Bucket>
      <Name>firmware-images</Name>
      <CreationDate>2025-01-10T08:00:00.000Z</CreationDate>
    </Bucket>
  </Buckets>
</ListAllMyBucketsResult>
```

Extract: `//Buckets/Bucket/Name`, `//Buckets/Bucket/CreationDate`.

### 1.2 ListObjectsV2 — `GET /{bucket}?list-type=2&prefix=...`

```
GET /firmware-images?list-type=2&prefix=zynq%2F&max-keys=1000&continuation-token=TOKEN HTTP/1.1
Host: minio.corp:9000
x-amz-date: 20260426T120000Z
x-amz-content-sha256: e3b0c44298...
Authorization: AWS4-HMAC-SHA256 ...
```

Key query parameters:
| Parameter | Description |
|---|---|
| `list-type=2` | Activates V2 API (required) |
| `prefix` | URI-encoded prefix filter |
| `max-keys` | 1–1000 (default 1000) |
| `continuation-token` | Pagination token from prior response |
| `delimiter` | Use `/` for directory-like listing |

Response XML:
```xml
<ListBucketResult>
  <Name>firmware-images</Name>
  <Prefix>zynq/</Prefix>
  <MaxKeys>1000</MaxKeys>
  <IsTruncated>true</IsTruncated>
  <NextContinuationToken>1Ue...abcd</NextContinuationToken>
  <Contents>
    <Key>zynq/v2.3.0/fw.bin</Key>
    <LastModified>2026-04-01T10:00:00.000Z</LastModified>
    <ETag>&quot;d41d8cd98f00b204e9800998ecf8427e&quot;</ETag>
    <Size>134217728</Size>
    <StorageClass>STANDARD</StorageClass>
  </Contents>
  <CommonPrefixes><Prefix>zynq/v2.3.0/</Prefix></CommonPrefixes>
</ListBucketResult>
```

Pagination: loop while `IsTruncated == true`, passing `NextContinuationToken` as
`continuation-token` in the next request.

### 1.3 GetObject — `GET /{bucket}/{key}`

```
GET /firmware-images/zynq/v2.3.0/fw.bin HTTP/1.1
Host: minio.corp:9000
Range: bytes=0-10485759          # optional — first 10 MiB
x-amz-date: 20260426T120000Z
x-amz-content-sha256: e3b0c44...
Authorization: AWS4-HMAC-SHA256 ...
```

Response (200 OK for full, 206 Partial Content for Range):
- `Content-Length`: byte count of body
- `Content-Type`: MIME type
- `ETag`: MD5 (or multipart variant) of object
- `Last-Modified`: RFC 7231 date

For large FW images, stream the response body in 8–16 MiB chunks to a local file descriptor
without buffering in RAM. Use `Range: bytes=START-END` for resumable downloads.

### 1.4 HeadObject — `HEAD /{bucket}/{key}`

```
HEAD /firmware-images/zynq/v2.3.0/fw.bin HTTP/1.1
Host: minio.corp:9000
x-amz-date: 20260426T120000Z
x-amz-content-sha256: e3b0c44...
Authorization: AWS4-HMAC-SHA256 ...
```

Response headers (no body):
- `Content-Length`: object size in bytes
- `Last-Modified`: ISO 8601 timestamp
- `ETag`: object hash
- `x-amz-meta-*`: user-defined metadata tags (e.g. `x-amz-meta-build-id: 1234`)
- `x-amz-tagging-count`: number of tags (use GetObjectTagging for values)

Use this for `stat_object` and `read_object_metadata` operations.

### 1.5 PutObject — `PUT /{bucket}/{key}`

```
PUT /firmware-images/zynq/v2.4.0/fw.bin HTTP/1.1
Host: minio.corp:9000
Content-Length: 134217728
Content-Type: application/octet-stream
x-amz-content-sha256: UNSIGNED-PAYLOAD    # or precomputed hex for small files
x-amz-date: 20260426T120000Z
x-amz-meta-build-id: 1234
Authorization: AWS4-HMAC-SHA256 ...

[binary body]
```

Rules:
- `Content-Length` is mandatory. Max single-PUT object: 5 GiB.
- Use `UNSIGNED-PAYLOAD` as the payload hash when streaming over HTTPS to avoid
  buffering the whole body for SHA256. Only the headers are signed.
- For files > 64 MiB, prefer multipart upload (see §5).
- `x-amz-meta-*` headers attach user metadata (lowercase keys, stored as-is).

### 1.6 GetObjectTagging — `GET /{bucket}/{key}?tagging`

HeadObject returns only `x-amz-tagging-count`. To retrieve tag key/value pairs, issue a
separate request:

```
GET /firmware-images/zynq/v2.3.0/fw.bin?tagging HTTP/1.1
Host: minio.corp:9000
x-amz-date: 20260426T120000Z
x-amz-content-sha256: e3b0c44298...
Authorization: AWS4-HMAC-SHA256 ...
```

Response XML (200 OK):
```xml
<Tagging>
  <TagSet>
    <Tag><Key>build-id</Key><Value>1234</Value></Tag>
    <Tag><Key>env</Key><Value>prod</Value></Tag>
  </TagSet>
</Tagging>
```

`stat_object()` returns size + last-modified from HeadObject; tag values are fetched via
`read_tags()` which calls this endpoint. Keeping them separate avoids the extra round-trip
when tags are not needed.

### 1.7 Presigned GET URL (no network call — client-side signing)

A presigned URL embeds authentication in query parameters so any HTTP client can fetch the
object without credentials. Max expiry: **604800 seconds (7 days)**.

Query parameters added to the base URL, sorted lexicographically:
```
X-Amz-Algorithm=AWS4-HMAC-SHA256
X-Amz-Credential=AKIAIOSFODNN7EXAMPLE%2F20260426%2Fus-east-1%2Fs3%2Faws4_request
X-Amz-Date=20260426T120000Z
X-Amz-Expires=86400
X-Amz-SignedHeaders=host
X-Amz-Signature=<computed>
```

Payload hash for presigned URLs: always use the literal string `UNSIGNED-PAYLOAD` in the
canonical request (not the actual body hash).

---

## 2. AWS Signature V4

Source: https://docs.aws.amazon.com/AmazonS3/latest/API/sigv4-query-string-auth.html

### 2.1 Algorithm Overview

```
signing_key = HMAC-SHA256(
                HMAC-SHA256(
                  HMAC-SHA256(
                    HMAC-SHA256("AWS4" + secret_access_key, date),
                    region),
                  service),
                "aws4_request")

signature = Hex(HMAC-SHA256(signing_key, string_to_sign))
```

Functions needed:
- `HMAC_SHA256(key: [u8], data: [u8]) -> [u8]` — 32-byte MAC
- `SHA256(data: [u8]) -> [u8]` — 32-byte hash
- `Hex(bytes: [u8]) -> str` — lowercase hex (64 chars for SHA256 output)
- `UriEncode(s: str, encode_slash: bool) -> str` — percent-encode, uppercase hex digits,
  space → `%20`, `/` encoded only in query values not in path.

### 2.2 Canonical Request

```
CanonicalRequest =
  HTTPMethod + "\n" +
  CanonicalURI + "\n" +
  CanonicalQueryString + "\n" +
  CanonicalHeaders + "\n" +
  SignedHeaders + "\n" +
  HexPayloadHash
```

- **CanonicalURI**: URI-encode each path segment (not slashes). Must be absolute (`/` if root).
- **CanonicalQueryString**: All query params sorted lexicographically by key, then by value.
  Key and value both URI-encoded. Joined with `&`.
- **CanonicalHeaders**: Lowercase header name + `:` + trimmed value + `\n`. Sorted by name.
  Must include `host` always. Include `x-amz-date`, `x-amz-content-sha256`, and any
  `x-amz-*` headers being sent.
- **SignedHeaders**: Semicolon-separated lowercase header names, same sort order. E.g.:
  `host;x-amz-content-sha256;x-amz-date`
- **HexPayloadHash**: `Hex(SHA256(body))` for known bodies; `UNSIGNED-PAYLOAD` for streaming
  PUTs over HTTPS; `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
  for empty body.

### 2.3 String to Sign

```
StringToSign =
  "AWS4-HMAC-SHA256" + "\n" +
  ISO8601DateTime + "\n" +          # e.g. 20260426T120000Z
  CredentialScope + "\n" +          # e.g. 20260426/us-east-1/s3/aws4_request
  Hex(SHA256(CanonicalRequest))
```

### 2.4 Authorization Header Format

```
Authorization: AWS4-HMAC-SHA256
  Credential=AKID/20260426/us-east-1/s3/aws4_request,
  SignedHeaders=host;x-amz-content-sha256;x-amz-date,
  Signature=<hex>
```

### 2.5 Worked Test Vector (Presigned GET — AWS Published Example)

Source: https://docs.aws.amazon.com/AmazonS3/latest/API/sigv4-query-string-auth.html

Inputs:
- Object: `test.txt` in bucket `examplebucket` (virtual-host style for AWS; swap to path-style for MinIO)
- Access key ID: `AKIAIOSFODNN7EXAMPLE`
- Secret: `wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY`
- Date: `20130524T000000Z`
- Region: `us-east-1`, Service: `s3`
- Expires: `86400`

Canonical Request:
```
GET
/test.txt
X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Credential=AKIAIOSFODNN7EXAMPLE%2F20130524%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Date=20130524T000000Z&X-Amz-Expires=86400&X-Amz-SignedHeaders=host
host:examplebucket.s3.amazonaws.com

host
UNSIGNED-PAYLOAD
```

String to Sign:
```
AWS4-HMAC-SHA256
20130524T000000Z
20130524/us-east-1/s3/aws4_request
3bfa292879f6447bbcda7001decf97f4a54dc650c8942174ae0a9121cf58ad04
```

Signing Key:
```
HMAC-SHA256(
  HMAC-SHA256(
    HMAC-SHA256(
      HMAC-SHA256("AWS4" + "wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY", "20130524"),
      "us-east-1"),
    "s3"),
  "aws4_request")
```

Final Signature: `aeeed9bbccd4d02ee5c0109b86d86835f995330da4c265957d157751f604d404`

Full presigned URL:
```
https://examplebucket.s3.amazonaws.com/test.txt
  ?X-Amz-Algorithm=AWS4-HMAC-SHA256
  &X-Amz-Credential=AKIAIOSFODNN7EXAMPLE%2F20130524%2Fus-east-1%2Fs3%2Faws4_request
  &X-Amz-Date=20130524T000000Z
  &X-Amz-Expires=86400
  &X-Amz-SignedHeaders=host
  &X-Amz-Signature=aeeed9bbccd4d02ee5c0109b86d86835f995330da4c265957d157751f604d404
```

For MinIO path-style, replace `examplebucket.s3.amazonaws.com/test.txt` with
`minio.corp:9000/examplebucket/test.txt` and update the `host` header and canonical URI
accordingly.

**Note on header-auth canonical request:** This vector uses query-string auth with
`UNSIGNED-PAYLOAD` and only the `host` signed header — its canonical request layout
differs from a header-authed GET (which includes `host;x-amz-content-sha256;x-amz-date`
in SignedHeaders and a real SHA256 payload hash). The HMAC-SHA256 chain and signing-key
derivation are identical in both modes and can be byte-compared against this vector.
For header-auth layout verification, see the AWS published `get-object` example at
https://docs.aws.amazon.com/general/latest/gr/sigv4-signed-request-examples.html

### 2.6 SigV4 Implementation Gotchas

1. **Date vs DateTime**: Signing key derivation uses `YYYYMMDD` (date only). `x-amz-date`
   header and StringToSign use `YYYYMMDDTHHmmssZ` (full ISO 8601, always UTC, no ms).
2. **UriEncode slash rule**: Encode `/` in query string values but NOT in the canonical URI
   path (each path segment is encoded individually, slashes preserved as separators).
3. **Header sort order**: Canonical headers must be sorted by lowercase name.
   `content-type` comes before `host` alphabetically.
4. **Trailing newline in CanonicalHeaders**: each header line ends with `\n` including the
   last one, so `SignedHeaders` line immediately follows without an extra blank line — the
   empty line in the canonical request is between `CanonicalHeaders` and `SignedHeaders`.
5. **UNSIGNED-PAYLOAD**: Use this for PUTs over HTTPS when you can't precompute the body
   SHA256 without buffering. The `x-amz-content-sha256: UNSIGNED-PAYLOAD` header must be
   signed (included in SignedHeaders).
6. **Canonical query string for presigned URLs**: All `X-Amz-*` parameters except
   `X-Amz-Signature` must be in the canonical query string and sorted.
7. **Credential encoding**: In presigned URLs, `/` in the credential must be encoded as
   `%2F` in the URL but appear literal in the CanonicalQueryString (the encoded form is
   what gets sorted and signed).
8. **Clock skew**: S3/MinIO rejects requests with timestamp > 15 minutes from server time.
   Log a clear error and surface the time delta.

---

## 3. Streaming Download and Upload

### 3.1 Streaming GET (large FW images)

- Issue a `Range: bytes=0-{chunk_size-1}` request to get the first chunk, check
  `Content-Range` response header for total size.
- Stream response body to a file descriptor in 8–16 MiB chunks, never loading entirely
  into RAM.
- For resumable downloads: check the local file size, then request `Range: bytes={local_size}-`.
  Verify ETag or Content-MD5 at completion.
- 206 Partial Content is success for ranged requests; 200 OK means server ignored the Range
  header (rare, treat as full response).

### 3.2 Streaming PUT

- Must know `Content-Length` before starting (stat the local file first).
- Use `x-amz-content-sha256: UNSIGNED-PAYLOAD` over HTTPS to avoid buffering for SHA256.
- Stream file in chunks from a file descriptor. Do NOT buffer entire file in RAM.
- Single PUT max: **5 GiB**. Above 64 MiB, use multipart (§5).

---

## 4. MinIO Admin API — Server Health

MinIO exposes a non-S3 health endpoint that does NOT require authentication:

```
GET /minio/health/live HTTP/1.1
Host: minio.corp:9000
```

Response: `200 OK` (server is alive) or `503 Service Unavailable` (degraded).

Source: https://min.io/docs/minio/linux/operations/monitoring/healthcheck-probe.html

The cluster-level readiness probe is at `GET /minio/health/cluster`. Both require no auth.
For the adapter, only `health/live` is needed.

---

## 5. Multipart Upload

Source: https://docs.aws.amazon.com/AmazonS3/latest/API/API_CreateMultipartUpload.html

Use multipart upload for files exceeding **64 MiB** (recommended threshold for FW images).

### 5.1 Limits

| Constraint | Value |
|---|---|
| Minimum part size | 5 MiB (except last part) |
| Maximum part size | 5 GiB |
| Maximum parts per upload | 10,000 |
| Maximum object size via multipart | 5 TiB |
| Single-PUT max | 5 GiB |

Recommended part size for FW images: **64 MiB** (fits 10,000 parts × 64 MiB = 640 GiB max).

### 5.2 Protocol — Three API Calls

**Step 1: Initiate**
```
POST /{bucket}/{key}?uploads HTTP/1.1
Host: minio.corp:9000
Content-Type: application/octet-stream
x-amz-date: ...
Authorization: ...
```
Response:
```xml
<InitiateMultipartUploadResult>
  <Bucket>firmware-images</Bucket>
  <Key>zynq/v2.4.0/fw.bin</Key>
  <UploadId>VXBsb2FkIElEIGZvciA2aWWpbmcncyBteS1tb3ZpZS5tMnRzIHVwbG9hZA</UploadId>
</InitiateMultipartUploadResult>
```

**Step 2: Upload Parts** (repeat for each 64 MiB chunk)
```
PUT /{bucket}/{key}?partNumber=1&uploadId=UPLOAD_ID HTTP/1.1
Content-Length: 67108864
x-amz-content-sha256: UNSIGNED-PAYLOAD
...
```
Response: `200 OK` with header `ETag: "etag-value"` — save each ETag.

**Step 3: Complete**
```
POST /{bucket}/{key}?uploadId=UPLOAD_ID HTTP/1.1
Content-Type: application/xml

<CompleteMultipartUpload>
  <Part><PartNumber>1</PartNumber><ETag>"etag1"</ETag></Part>
  <Part><PartNumber>2</PartNumber><ETag>"etag2"</ETag></Part>
</CompleteMultipartUpload>
```
Response:
```xml
<CompleteMultipartUploadResult>
  <Location>https://...</Location>
  <Bucket>firmware-images</Bucket>
  <Key>zynq/v2.4.0/fw.bin</Key>
  <ETag>"final-etag"</ETag>
</CompleteMultipartUploadResult>
```

On failure: call `DELETE /{bucket}/{key}?uploadId=UPLOAD_ID` to abort and free storage.

---

## 6. TLS / HTTPS Verification

On-prem MinIO commonly uses self-signed certificates. The adapter config struct must expose
a `tls_skip_verify: bool` knob, defaulting to `false`.

```
# Config struct (conceptual)
struct MinioConfig {
    endpoint: str         # e.g. "https://minio.corp:9000"
    access_key: str
    secret_key: str
    region: str           # MinIO default: "us-east-1"
    tls_skip_verify: bool # default: false — must be explicit opt-in
    presign_base_url: str # override for presigned URL base (optional)
}
```

Implementation notes:
- When `tls_skip_verify = true`, emit a warning log at startup: `"[WARN] MinIO TLS verify
  disabled — not safe for production"`.
- The HTTP client (Simple runtime FFI) must plumb this to the TLS context.
- For presigned URL generation, the URL uses whatever scheme/host is in `endpoint`; no TLS
  connection is made during URL generation itself.
- Never silently skip TLS verification based on URL pattern or other heuristics.

---

## Decisions for Adapter

1. **Path-style only**: Use `https://HOST:PORT/{bucket}/{key}` everywhere. Do not support
   virtual-host style. Document this as a known limitation for AWS S3 (which deprecated
   path-style), but it's the correct default for MinIO.

2. **Payload hash strategy**: Use `UNSIGNED-PAYLOAD` for all PUTs over HTTPS (avoids
   buffering). Use `e3b0c44...` (SHA256 of empty string) for GET/HEAD/DELETE. Precompute
   SHA256 only for small ListObjects/CreateMultipart XML bodies that fit in RAM.

3. **Streaming threshold**: Multipart upload for files > 64 MiB. Part size: 64 MiB.
   Single-threaded sequential parts (no parallel parts needed at MVP).

4. **Range download**: Always check `Content-Range` response header. Support resumable
   downloads by checking local file size before starting. Chunk size for streaming: 8 MiB.

5. **Presigned URL max expiry**: Cap at 604800 seconds (7 days). Return error if caller
   requests longer. Default expiry: 86400 seconds (1 day).

6. **MinIO health check**: `GET /minio/health/live` (no auth). Return `bool` from
   `health_live()` — true if 200, false otherwise.

7. **TLS verification**: Default `tls_skip_verify = false`. Warn loudly when disabled.
   Never infer skip-verify from cert errors silently.

8. **Error mapping**: Parse HTTP status codes: 403 → auth error, 404 → not found, 409 →
   conflict (e.g. bucket exists), 503 → server unavailable. Parse `<Error><Code>...</Code>
   <Message>...</Message></Error>` XML body for detail.

9. **Region for MinIO**: MinIO accepts any region string. Default to `"us-east-1"` if not
   configured — it still works. Make it configurable.

10. **Clock skew guard**: If server returns 403 with `RequestTimeTooSkewed`, log the
    detected delta and surface a clear error. Do not retry automatically.

11. **Tag retrieval**: `stat_object()` calls HeadObject only (size, last-modified, etag,
    tag count). `read_tags()` calls GetObjectTagging (`?tagging`) for full key/value pairs.
    Keep separate to avoid extra round-trips when tags are not needed.
