# Blink URL Parser Specification

> Tests for the Blink-style WHATWG URL parser subset (mirrors Chromium's url::GURL). Covers absolute URL shape parsing (scheme + authority + path + query + fragment), percent-encoding/decoding round-trips, and the application/x-www-form-urlencoded query_string_parse splitter.

<!-- sdn-diagram:id=url_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=url_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

url_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=url_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink URL Parser Specification

Tests for the Blink-style WHATWG URL parser subset (mirrors Chromium's url::GURL). Covers absolute URL shape parsing (scheme + authority + path + query + fragment), percent-encoding/decoding round-trips, and the application/x-www-form-urlencoded query_string_parse splitter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/url/url_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style WHATWG URL parser subset (mirrors Chromium's
url::GURL). Covers absolute URL shape parsing (scheme + authority + path +
query + fragment), percent-encoding/decoding round-trips, and the
application/x-www-form-urlencoded query_string_parse splitter.

## Scenarios

### parse_url scheme and host

#### extracts scheme=https and host=example.com

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = parse_url("https://example.com")
expect(u.scheme).to_equal("https")
expect(u.host).to_equal("example.com")
expect(u.is_valid).to_equal(true)
```

</details>

### parse_url authority port and path

#### extracts port=8080 and path=/path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = parse_url("https://example.com:8080/path")
expect(u.host).to_equal("example.com")
expect(u.port).to_equal(8080)
expect(u.path).to_equal("/path")
expect(u.is_valid).to_equal(true)
```

</details>

### parse_url query

#### extracts query a=1&b=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = parse_url("https://example.com/?a=1&b=2")
expect(u.query).to_equal("a=1&b=2")
expect(u.path).to_equal("/")
expect(u.is_valid).to_equal(true)
```

</details>

### parse_url fragment

#### extracts fragment=section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = parse_url("https://example.com/#section")
expect(u.fragment).to_equal("section")
expect(u.is_valid).to_equal(true)
```

</details>

### percent_decode

#### %20 decodes to a single space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoded = percent_decode("%20")
expect(decoded).to_equal(" ")
expect(decoded.len().to_i64()).to_equal(1)
```

</details>

### percent_encode

#### space is encoded to %20 when not in allowed list

1. allowed push
2. allowed push
   - Expected: encoded equals `A%20B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allowed: [i64] = [i64]()
allowed.push(65)  # 'A'
allowed.push(66)  # 'B'
val encoded = percent_encode("A B", allowed)
expect(encoded).to_equal("A%20B")
expect(encoded.len().to_i64()).to_be_greater_than(3)
```

</details>

### query_string_parse

#### splits a=1&b=2 into two pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = query_string_parse("a=1&b=2")
expect(pairs.len().to_i64()).to_equal(2)
val p0 = pairs[0]
val p1 = pairs[1]
expect(p0.0).to_equal("a")
expect(p0.1).to_equal("1")
expect(p1.0).to_equal("b")
expect(p1.1).to_equal("2")
```

</details>

### parse_url empty

#### empty string yields is_valid=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = parse_url("")
expect(u.is_valid).to_equal(false)
expect(u.scheme).to_equal("")
expect(u.host).to_equal("")
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
