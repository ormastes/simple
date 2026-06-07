# HTTP Hardening Specification

> <details>

<!-- sdn-diagram:id=http_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=http_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

http_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=http_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTP Hardening Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-1, #AC-2, #AC-3, #AC-4 |
| Category | Stdlib / Security |
| Difficulty | 3/5 |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http/http_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### HTTP request parser limits (AC-1)

#### accepts request line within default limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val line = "GET /index.html HTTP/1.1"
val err = check_request_line(line, limits)
expect(err.?).to_equal(false)
```

</details>

#### rejects request line exceeding 8192 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
var long_path = "GET /"
var i = 0
while i < 8200:
    long_path = long_path + "a"
    i = i + 1
long_path = long_path + " HTTP/1.1"
val err = check_request_line(long_path, limits)
expect(err.?).to_equal(true)
val status = http_parse_error_status(err.unwrap())
expect(status).to_equal(414)
```

</details>

#### rejects malformed request line with fewer than 3 parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val err = check_request_line("BADREQUEST", limits)
expect(err.?).to_equal(true)
val status = http_parse_error_status(err.unwrap())
expect(status).to_equal(400)
```

</details>

#### accepts header count within limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val err = check_header_count(50, limits)
expect(err.?).to_equal(false)
```

</details>

#### rejects header count exceeding 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val err = check_header_count(101, limits)
expect(err.?).to_equal(true)
val status = http_parse_error_status(err.unwrap())
expect(status).to_equal(400)
```

</details>

#### accepts header size within limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val err = check_header_size("Content-Type", "application/json", limits)
expect(err.?).to_equal(false)
```

</details>

#### rejects header exceeding 8192 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
var big_value = ""
var i = 0
while i < 8200:
    big_value = big_value + "x"
    i = i + 1
val err = check_header_size("X-Big", big_value, limits)
expect(err.?).to_equal(true)
val status = http_parse_error_status(err.unwrap())
expect(status).to_equal(400)
```

</details>

#### accepts body size within 10MB limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val err = check_body_size(1024, limits)
expect(err.?).to_equal(false)
```

</details>

#### rejects body exceeding 10MB

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
val err = check_body_size(10485761, limits)
expect(err.?).to_equal(true)
val status = http_parse_error_status(err.unwrap())
expect(status).to_equal(413)
```

</details>

#### supports custom limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = HttpLimits(
    max_request_line_bytes: 256,
    max_header_count: 10,
    max_header_size_bytes: 512,
    max_body_bytes: 1024,
    idle_timeout_seconds: 30,
    max_requests_per_connection: 50
)
val err = check_request_line("GET /short HTTP/1.1", limits)
expect(err.?).to_equal(false)
val count_err = check_header_count(11, limits)
expect(count_err.?).to_equal(true)
```

</details>

### Path traversal refusal (AC-2)

#### accepts normal paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_safe_static_path("/index.html")).to_equal(true)
expect(is_safe_static_path("/css/style.css")).to_equal(true)
expect(is_safe_static_path("/images/logo.png")).to_equal(true)
```

</details>

#### rejects double-dot traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_safe_static_path("/../etc/passwd")).to_equal(false)
expect(is_safe_static_path("/css/../../secret")).to_equal(false)
expect(contains_traversal("/../etc/passwd")).to_equal(true)
```

</details>

#### rejects dot-slash sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_safe_static_path("/./etc/passwd")).to_equal(false)
expect(contains_traversal("/./etc/passwd")).to_equal(true)
```

</details>

#### rejects null bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_null_byte("/index.html\0.txt")).to_equal(true)
expect(is_safe_static_path("/index.html\0.txt")).to_equal(false)
```

</details>

#### rejects backslash paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_backslash("/css\\..\\secret")).to_equal(true)
expect(is_safe_static_path("/css\\..\\secret")).to_equal(false)
```

</details>

#### rejects paths not starting with slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_safe_static_path("etc/passwd")).to_equal(false)
expect(is_safe_static_path("")).to_equal(false)
```

</details>

#### normalizes safe paths

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_static_path("/css/style.css")
match result:
    case Ok(normalized):
        expect(normalized).to_equal("/css/style.css")
    case Err(msg):
        fail("validate_static_path rejected a safe path: {msg}")
```

</details>

#### rejects traversal via validate_static_path

1. fail
   - Expected: msg contains `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_static_path("/../secret")
match result:
    case Ok(normalized):
        fail("validate_static_path accepted traversal path")
    case Err(msg):
        expect(msg.contains("rejected")).to_equal(true)
```

</details>

### Header canonicalization and duplicate policy (AC-3)

#### normalizes header names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_header_name("content-type")).to_equal("Content-Type")
expect(normalize_header_name("x-forwarded-for")).to_equal("X-Forwarded-For")
expect(normalize_header_name("HOST")).to_equal("Host")
```

</details>

#### canonicalizes a list of headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [("content-type", "text/html"), ("x-custom", "val")]
val canon = canonicalize_headers(headers)
expect(canon[0][0]).to_equal("Content-Type")
expect(canon[1][0]).to_equal("X-Custom")
```

</details>

#### identifies singleton headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_singleton_header("Content-Type")).to_equal(true)
expect(is_singleton_header("Host")).to_equal(true)
expect(is_singleton_header("X-Custom")).to_equal(false)
expect(is_singleton_header("Set-Cookie")).to_equal(false)
```

</details>

#### deduplicates singleton headers with last-wins

1.
2.
3.
4.
   - Expected: ct_count equals `1`
   - Expected: ct_value equals `application/json`
   - Expected: xc_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [
    ("Content-Type", "text/html"),
    ("X-Custom", "a"),
    ("Content-Type", "application/json"),
    ("X-Custom", "b")
]
val deduped = deduplicate_headers_last_wins(headers)
var ct_count = 0
var ct_value = ""
var xc_count = 0
var i = 0
while i < deduped.length():
    if deduped[i][0].lower() == "content-type":
        ct_count = ct_count + 1
        ct_value = deduped[i][1]
    if deduped[i][0].lower() == "x-custom":
        xc_count = xc_count + 1
    i = i + 1
expect(ct_count).to_equal(1)
expect(ct_value).to_equal("application/json")
expect(xc_count).to_equal(2)
```

</details>

#### validates no duplicate singletons

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val good = [("Content-Type", "text/html"), ("Host", "example.com")]
val good_result = validate_no_duplicate_singletons(good)
match good_result:
    case Ok(h): expect(h.length()).to_equal(2)
    case Err(msg): fail("validate_no_duplicate_singletons rejected unique singleton headers: {msg}")

val bad = [("Host", "a.com"), ("Host", "b.com")]
val bad_result = validate_no_duplicate_singletons(bad)
match bad_result:
    case Ok(h): fail("validate_no_duplicate_singletons accepted duplicate Host headers")
    case Err(msg): expect(msg.contains("duplicate")).to_equal(true)
```

</details>

### Connection limits configuration (AC-4)

#### default limits have sensible values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
expect(limits.idle_timeout_seconds).to_equal(60)
expect(limits.max_requests_per_connection).to_equal(100)
```

</details>

#### custom limits are respected

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = HttpLimits(
    max_request_line_bytes: 4096,
    max_header_count: 50,
    max_header_size_bytes: 4096,
    max_body_bytes: 1048576,
    idle_timeout_seconds: 30,
    max_requests_per_connection: 50
)
expect(limits.idle_timeout_seconds).to_equal(30)
expect(limits.max_requests_per_connection).to_equal(50)
```

</details>

#### error messages are descriptive

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = HttpParseError.RequestLineTooLong(9000, 8192)
val msg = http_parse_error_message(err)
expect(msg.contains("9000")).to_equal(true)
expect(msg.contains("8192")).to_equal(true)

val body_err = HttpParseError.BodyTooLarge(20000000, 10485760)
val body_msg = http_parse_error_message(body_err)
expect(body_msg.contains("too large")).to_equal(true)
```

</details>

### Hardening enforcement — no unbounded claims (AC-5)

#### default limits bound request line size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
expect(limits.max_request_line_bytes > 0).to_equal(true)
expect(limits.max_request_line_bytes <= 65536).to_equal(true)
```

</details>

#### default limits bound header count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
expect(limits.max_header_count > 0).to_equal(true)
expect(limits.max_header_count <= 1000).to_equal(true)
```

</details>

#### default limits bound body size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
expect(limits.max_body_bytes > 0).to_equal(true)
expect(limits.max_body_bytes <= 104857600).to_equal(true)
```

</details>

#### default limits bound connection lifetime

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
expect(limits.idle_timeout_seconds > 0).to_equal(true)
expect(limits.idle_timeout_seconds <= 3600).to_equal(true)
```

</details>

#### default limits bound requests per connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = http_limits_default()
expect(limits.max_requests_per_connection > 0).to_equal(true)
expect(limits.max_requests_per_connection <= 10000).to_equal(true)
```

</details>

#### zero-value limits reject all input

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = HttpLimits(
    max_request_line_bytes: 0,
    max_header_count: 0,
    max_header_size_bytes: 0,
    max_body_bytes: 0,
    idle_timeout_seconds: 1,
    max_requests_per_connection: 1
)
val line_err = check_request_line("GET / HTTP/1.1", limits)
expect(line_err.?).to_equal(true)
val hdr_err = check_header_count(1, limits)
expect(hdr_err.?).to_equal(true)
val body_err = check_body_size(1, limits)
expect(body_err.?).to_equal(true)
```

</details>

#### path traversal is always rejected regardless of limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_safe_static_path("/../../../etc/shadow")).to_equal(false)
expect(is_safe_static_path("/..\\secret")).to_equal(false)
expect(is_safe_static_path("/good/../../../bad")).to_equal(false)
```

</details>

#### normalize_path removes redundant slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val norm = normalize_path("/css//style.css")
expect(norm.contains("//")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
