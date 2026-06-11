# request_validation_spec

> Tests for request path validation and URI safety checks. Validates rejection of path traversal, null bytes, and overly long URIs.

<!-- sdn-diagram:id=request_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=request_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

request_validation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=request_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# request_validation_spec

Tests for request path validation and URI safety checks. Validates rejection of path traversal, null bytes, and overly long URIs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-013 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/request_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for request path validation and URI safety checks.
Validates rejection of path traversal, null bytes, and overly long URIs.

## Scenarios

### Request path validation

#### rejects path traversal with ../

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/../etc/passwd")
expect(result).to_equal(false)
```

</details>

#### rejects path traversal with encoded ../

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/%2e%2e/etc/passwd")
expect(result).to_equal(false)
```

</details>

#### rejects path traversal in middle of path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/api/../admin/secret")
expect(result).to_equal(false)
```

</details>

### Null byte rejection

#### rejects null bytes in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/api/resource\x00.html"
val result = validate_request_path(path)
expect(result).to_equal(false)
```

</details>

### Valid path acceptance

#### accepts normal paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/api/users/123")
expect(result).to_equal(true)
```

</details>

#### accepts root path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/")
expect(result).to_equal(true)
```

</details>

#### accepts path with query string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/search?q=hello")
expect(result).to_equal(true)
```

</details>

#### accepts path with dots in filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_request_path("/static/style.min.css")
expect(result).to_equal(true)
```

</details>

### URI length validation

#### rejects overly long URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_uri = "/"
var i = 0
while i < 10000:
    long_uri = long_uri + "a"
    i = i + 1
val result = validate_uri_length(long_uri, default_max_uri_length())
expect(result).to_equal(false)
```

</details>

#### accepts normal length URIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate_uri_length("/api/data", default_max_uri_length())
expect(result).to_equal(true)
```

</details>

#### default max URI length is reasonable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_len = default_max_uri_length()
val is_reasonable = max_len > 0 and max_len <= 65536
expect(is_reasonable).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
