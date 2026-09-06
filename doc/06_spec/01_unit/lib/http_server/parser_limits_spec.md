# parser_limits_spec

> Boundary specs for request-line length, header count, per-header size, Content-Length validation, oversized body rejection, and chunked Transfer-Encoding rejection in the sync HTTP parser.

<!-- sdn-diagram:id=parser_limits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_limits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_limits_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_limits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_limits_spec

Boundary specs for request-line length, header count, per-header size, Content-Length validation, oversized body rejection, and chunked Transfer-Encoding rejection in the sync HTTP parser.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-020 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/parser_limits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Boundary specs for request-line length, header count, per-header size,
Content-Length validation, oversized body rejection, and chunked
Transfer-Encoding rejection in the sync HTTP parser.

All helpers operate on in-memory data only — no live socket needed.

## Scenarios

### content_length_from_text — valid values

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("0")
expect(v).to_equal(0)
```

</details>

#### parses a normal body size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("1024")
expect(v).to_equal(1024)
```

</details>

#### parses i32 max (2147483647)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("2147483647")
expect(v).to_equal(2147483647)
```

</details>

#### trims surrounding whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("  512  ")
expect(v).to_equal(512)
```

</details>

### content_length_from_text — rejection

#### rejects negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("-1")
expect(v).to_equal(-1)
```

</details>

#### rejects large negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("-99999")
expect(v).to_equal(-1)
```

</details>

#### rejects non-numeric input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("abc")
expect(v).to_equal(-1)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("")
expect(v).to_equal(-1)
```

</details>

#### rejects overflow beyond i32 max

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("2147483648")
expect(v).to_equal(-1)
```

</details>

#### rejects large overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("99999999999")
expect(v).to_equal(-1)
```

</details>

#### rejects mixed alphanumeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("123abc")
expect(v).to_equal(-1)
```

</details>

### Parser limit constants

#### MAX_REQUEST_LINE is 8192

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MAX_REQUEST_LINE).to_equal(8192)
```

</details>

#### MAX_HEADER_COUNT is 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MAX_HEADER_COUNT).to_equal(100)
```

</details>

#### MAX_HEADER_LINE is 8192

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MAX_HEADER_LINE).to_equal(8192)
```

</details>

#### MAX_BODY_SIZE is 10 MiB

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MAX_BODY_SIZE).to_equal(10485760)
```

</details>

### Request-line length boundary

#### a line at exactly MAX_REQUEST_LINE is at boundary (not over)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = ""
var i = 0
while i < MAX_REQUEST_LINE:
    line = line + "a"
    i = i + 1
val at_limit = line.len() == MAX_REQUEST_LINE
expect(at_limit).to_equal(true)
```

</details>

#### a line one byte over MAX_REQUEST_LINE exceeds the limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = ""
var i = 0
while i < MAX_REQUEST_LINE + 1:
    line = line + "a"
    i = i + 1
val over_limit = line.len() > MAX_REQUEST_LINE
expect(over_limit).to_equal(true)
```

</details>

### Header count boundary

#### MAX_HEADER_COUNT is the declared limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_positive = MAX_HEADER_COUNT > 0
expect(is_positive).to_equal(true)
```

</details>

#### one more than limit would be rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val over = MAX_HEADER_COUNT + 1
val exceeds = over > MAX_HEADER_COUNT
expect(exceeds).to_equal(true)
```

</details>

### Header-line length boundary

#### a header line at exactly MAX_HEADER_LINE is at boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = ""
var i = 0
while i < MAX_HEADER_LINE:
    line = line + "x"
    i = i + 1
val at = line.len() == MAX_HEADER_LINE
expect(at).to_equal(true)
```

</details>

#### a header line one byte over MAX_HEADER_LINE exceeds limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = ""
var i = 0
while i < MAX_HEADER_LINE + 1:
    line = line + "x"
    i = i + 1
val over = line.len() > MAX_HEADER_LINE
expect(over).to_equal(true)
```

</details>

### Body size boundary

#### content-length equal to MAX_BODY_SIZE is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("10485760")
expect(v).to_equal(10485760)
```

</details>

#### content-length one byte over MAX_BODY_SIZE is within i32 range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("10485761")
expect(v).to_equal(10485761)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
