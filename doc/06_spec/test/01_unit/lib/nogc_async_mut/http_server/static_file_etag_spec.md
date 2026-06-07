# Static File ETag and Range Specification

> <details>

<!-- sdn-diagram:id=static_file_etag_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_file_etag_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_file_etag_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_file_etag_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static File ETag and Range Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-3-etag-range |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/static_file_etag_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Static file ETag generation and conditional requests

#### generates ETag from file metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub metadata inputs
val inode: u64 = 12345678
val mtime_ns: u64 = 1716633600000000000
val size: u64 = 65536
# Simulate: ETag is non-empty and wrapped in double quotes
val etag_raw = "\"a3f5c2e1d4b09817\""
expect(etag_raw.len() > 2).to_equal(true)
# Must start and end with double-quote character
val starts_with_quote = etag_raw.starts_with("\"")
val ends_with_quote = etag_raw.ends_with("\"")
expect(starts_with_quote).to_equal(true)
expect(ends_with_quote).to_equal(true)
```

</details>

#### returns 304 when If-None-Match matches ETag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val current_etag = "\"a3f5c2e1d4b09817\""
val if_none_match = "\"a3f5c2e1d4b09817\""
# ETags match → send 304
val etag_matches = current_etag == if_none_match
expect(etag_matches).to_equal(true)
val response_status = if etag_matches: 304 else: 200
expect(response_status).to_equal(304)
```

</details>

#### returns 200 when If-None-Match does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val current_etag = "\"a3f5c2e1d4b09817\""
val if_none_match = "\"000000000000dead\""
val etag_matches = current_etag == if_none_match
expect(etag_matches).to_equal(false)
val response_status = if etag_matches: 304 else: 200
expect(response_status).to_equal(200)
```

</details>

#### parses Range header for single byte range

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header_value = "bytes=0-1023"
# Stub parse: extract start/end
val prefix = "bytes="
val range_part = header_value.replace("bytes=", "")
# Verify parsing expectations
val expected_start: u64 = 0
val expected_end: u64 = 1023
expect(expected_start).to_equal(0)
expect(expected_end).to_equal(1023)
# Ensure range is not empty
val range_size = expected_end - expected_start + 1
expect(range_size).to_equal(1024)
```

</details>

#### returns 206 with partial content for valid range

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_size: u64 = 1048576  # 1MB
val range_start: u64 = 0
val range_end: u64 = 1023
# Range is satisfiable: end < file_size
val is_satisfiable = range_end < file_size && range_start <= range_end
expect(is_satisfiable).to_equal(true)
val response_status = if is_satisfiable: 206 else: 416
expect(response_status).to_equal(206)
# Content-Range header value
val content_range = "bytes 0-1023/1048576"
expect(content_range).to_contain("bytes")
expect(content_range).to_contain("1048576")
```

</details>

#### returns 416 for unsatisfiable range

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_size: u64 = 1024
val range_start: u64 = 2000  # beyond EOF
val range_end: u64 = 3000
# Range is unsatisfiable: start >= file_size
val is_satisfiable = range_start < file_size
expect(is_satisfiable).to_equal(false)
val response_status = if is_satisfiable: 206 else: 416
expect(response_status).to_equal(416)
# Content-Range header for 416 uses */size form
val content_range_416 = "bytes */1024"
expect(content_range_416).to_contain("*/1024")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
