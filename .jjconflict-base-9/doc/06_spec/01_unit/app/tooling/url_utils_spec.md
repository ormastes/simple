# Url Utils Specification

> 1. expect url encode

<!-- sdn-diagram:id=url_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=url_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

url_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=url_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Url Utils Specification

## Scenarios

### URL Utilities

### URL Encoding

#### encodes simple string

1. expect url encode


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect url_encode("hello") == "hello"
```

</details>

#### encodes space

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = url_encode("hello world")
expect result.contains("%20")
```

</details>

#### encodes special chars

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = url_encode("a+b")
expect result.contains("%")
```

</details>

### URL Decoding

#### decodes simple string

1. expect url decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect url_decode("hello") == "hello"
```

</details>

#### decodes percent-encoded space

1. expect url decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect url_decode("hello%20world") == "hello world"
```

</details>

#### decodes plus as space

1. expect url decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect url_decode("hello+world") == "hello world"
```

</details>

#### round-trip encode/decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello world"
val encoded = url_encode(original)
val decoded = url_decode(encoded)
expect decoded == original
```

</details>

### Character Codes

#### gets char code for letters

1. expect char code
2. expect char code
3. expect char code
4. expect char code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect char_code("A") == 65
expect char_code("a") == 97
expect char_code("Z") == 90
expect char_code("z") == 122
```

</details>

#### gets char code for digits

1. expect char code
2. expect char code


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect char_code("0") == 48
expect char_code("9") == 57
```

</details>

#### converts from char code

1. expect from char code
2. expect from char code
3. expect from char code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect from_char_code(65) == "A"
expect from_char_code(97) == "a"
expect from_char_code(48) == "0"
```

</details>

#### round-trip char code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code("A")
val ch = from_char_code(code)
expect ch == "A"
```

</details>

### Hex Conversion

#### converts to hex

1. expect to hex
2. expect to hex
3. expect to hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect to_hex(0) == "00"
expect to_hex(15) == "0F"
expect to_hex(255) == "FF"
```

</details>

#### converts hex digit

1. expect hex digit
2. expect hex digit
3. expect hex digit
4. expect hex digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect hex_digit(0) == "0"
expect hex_digit(9) == "9"
expect hex_digit(10) == "A"
expect hex_digit(15) == "F"
```

</details>

#### parses valid hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match from_hex("00"):
    case Some(n): expect n == 0
    case nil: expect false
match from_hex("FF"):
    case Some(n): expect n == 255
    case nil: expect false
```

</details>

#### returns nil for invalid hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match from_hex("GG"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### parses hex digit value

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match hex_digit_value("0"):
    case Some(n): expect n == 0
    case nil: expect false
match hex_digit_value("F"):
    case Some(n): expect n == 15
    case nil: expect false
match hex_digit_value("f"):
    case Some(n): expect n == 15
    case nil: expect false
```

</details>

### URL Parsing

#### parses simple URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("http://example.com"):
    case Some(url):
        expect url.scheme == "http"
        expect url.host == "example.com"
        expect url.path == "/"
    case nil: expect false
```

</details>

#### parses URL with path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("https://example.com/path/to/resource"):
    case Some(url):
        expect url.scheme == "https"
        expect url.host == "example.com"
        expect url.path == "/path/to/resource"
    case nil: expect false
```

</details>

#### parses URL with port

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("http://example.com:8080/"):
    case Some(url):
        expect url.host == "example.com"
        match url.port:
            case Some(p): expect p == 8080
            case nil: expect false
    case nil: expect false
```

</details>

#### parses URL with query

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("http://example.com/path?key=value"):
    case Some(url):
        expect url.path == "/path"
        expect url.query == "key=value"
    case nil: expect false
```

</details>

#### parses URL with fragment

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("http://example.com/page#section"):
    case Some(url):
        expect url.path == "/page"
        expect url.fragment == "section"
    case nil: expect false
```

</details>

#### parses URL with username

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("http://user@example.com/"):
    case Some(url):
        expect url.username == "user"
        expect url.host == "example.com"
    case nil: expect false
```

</details>

#### parses URL with credentials

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("ftp://user:pass@example.com/"):
    case Some(url):
        expect url.username == "user"
        expect url.password == "pass"
        expect url.host == "example.com"
    case nil: expect false
```

</details>

#### parses complete URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("https://user:pass@example.com:443/path?key=val#frag"):
    case Some(url):
        expect url.scheme == "https"
        expect url.username == "user"
        expect url.password == "pass"
        expect url.host == "example.com"
        match url.port:
            case Some(p): expect p == 443
            case nil: expect false
        expect url.path == "/path"
        expect url.query == "key=val"
        expect url.fragment == "frag"
    case nil: expect false
```

</details>

#### returns nil for invalid URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_url("not-a-url"):
    case Some(_): expect false
    case nil: expect true
```

</details>

### URL Building

#### builds simple URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "http",
    username: "",
    password-field: "",
    host: "example.com",
    port: nil,
    path: "/",
    query: "",
    fragment: ""
)
val result = build_url(url)
expect result == "http://example.com/"
```

</details>

#### builds URL with port

1. port: Some
2. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "http",
    username: "",
    password-field: "",
    host: "example.com",
    port: Some(8080),
    path: "/",
    query: "",
    fragment: ""
)
val result = build_url(url)
expect result.contains(":8080")
```

</details>

#### omits default port

1. port: Some
2. expect not result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "http",
    username: "",
    password-field: "",
    host: "example.com",
    port: Some(80),
    path: "/",
    query: "",
    fragment: ""
)
val result = build_url(url)
expect not result.contains(":80")
```

</details>

#### builds URL with query

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "https",
    username: "",
    password-field: "",
    host: "example.com",
    port: nil,
    path: "/search",
    query: "q=test",
    fragment: ""
)
val result = build_url(url)
expect result.contains("?q=test")
```

</details>

#### checks default port

1. expect is default port
2. expect is default port
3. expect is default port
4. expect not is default port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_default_port("http", 80)
expect is_default_port("https", 443)
expect is_default_port("ftp", 21)
expect not is_default_port("http", 8080)
```

</details>

### Query String

#### parses simple query

1. expect params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = parse_query_string("key=value")
expect params.len() == 1
expect params[0].0 == "key"
expect params[0].1 == "value"
```

</details>

#### parses multiple params

1. expect params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = parse_query_string("a=1&b=2&c=3")
expect params.len() == 3
expect params[0].0 == "a"
expect params[1].0 == "b"
expect params[2].0 == "c"
```

</details>

#### parses empty value

1. expect params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = parse_query_string("key=")
expect params.len() == 1
expect params[0].0 == "key"
expect params[0].1 == ""
```

</details>

#### parses no value

1. expect params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = parse_query_string("flag")
expect params.len() == 1
expect params[0].0 == "flag"
expect params[0].1 == ""
```

</details>

#### parses empty string

1. expect params len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = parse_query_string("")
expect params.len() == 0
```

</details>

#### builds simple query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = [("key", "value")]
val result = build_query_string(params)
expect result == "key=value"
```

</details>

#### builds multiple params

1. expect result contains
2. expect result contains
3. expect result contains
4. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = [("a", "1"), ("b", "2"), ("c", "3")]
val result = build_query_string(params)
expect result.contains("a=1")
expect result.contains("b=2")
expect result.contains("c=3")
expect result.contains("&")
```

</details>

#### builds with encoding

1. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = [("key", "hello world")]
val result = build_query_string(params)
expect result.contains("%20")
```

</details>

#### adds param to empty query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_query_param(query="", key="key", value="value")
expect result == "key=value"
```

</details>

#### adds param to existing query

1. expect result contains
2. expect result contains
3. expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_query_param(query="a=1", key="b", value="2")
expect result.contains("a=1")
expect result.contains("b=2")
expect result.contains("&")
```

</details>

### URL Validation

#### validates valid URLs

1. expect is valid url
2. expect is valid url
3. expect is valid url


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_valid_url("http://example.com")
expect is_valid_url("https://example.com/path")
expect is_valid_url("ftp://files.example.com")
```

</details>

#### rejects invalid URLs

1. expect not is valid url
2. expect not is valid url
3. expect not is valid url


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not is_valid_url("example.com")
expect not is_valid_url("/path/to/file")
expect not is_valid_url("http:example.com")
```

</details>

#### checks absolute URL

1. expect is absolute url
2. expect is absolute url
3. expect not is absolute url
4. expect not is absolute url


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_absolute_url("http://example.com")
expect is_absolute_url("https://example.com/path")
expect not is_absolute_url("/path/to/file")
expect not is_absolute_url("relative/path")
```

</details>

#### checks relative URL

1. expect is relative url
2. expect is relative url
3. expect not is relative url


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_relative_url("/path/to/file")
expect is_relative_url("relative/path")
expect not is_relative_url("http://example.com")
```

</details>

### URL Operations

#### gets base URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "https",
    username: "",
    password-field: "",
    host: "example.com",
    port: nil,
    path: "/path",
    query: "key=value",
    fragment: "section"
)
val base = get_base_url(url)
expect base == "https://example.com"
```

</details>

#### gets base URL with port

1. port: Some
2. expect base contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "http",
    username: "",
    password-field: "",
    host: "example.com",
    port: Some(8080),
    path: "/",
    query: "",
    fragment: ""
)
val base = get_base_url(url)
expect base.contains(":8080")
```

</details>

#### gets full path

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = Url(
    scheme: "https",
    username: "",
    password-field: "",
    host: "example.com",
    port: nil,
    path: "/path",
    query: "key=value",
    fragment: "section"
)
val full_path = get_full_path(url)
expect full_path == "/path?key=value#section"
```

</details>

#### joins absolute URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = join_url(base="http://example.com", rel="https://other.com/path")
expect result == "https://other.com/path"
```

</details>

#### joins relative URL with slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = join_url(base="http://example.com/", rel="/path")
expect result == "http://example.com/path"
```

</details>

#### joins relative URL without slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = join_url(base="http://example.com", rel="path")
expect result == "http://example.com/path"
```

</details>

#### joins both slashes

1. expect not result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = join_url(base="http://example.com/", rel="/path")
expect not result.contains("//path")
```

</details>

### Integer Parsing

#### parses valid int

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_int("123"):
    case Some(n): expect n == 123
    case nil: expect false
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_int("0"):
    case Some(n): expect n == 0
    case nil: expect false
```

</details>

#### returns nil for invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_int("abc"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_int(""):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Unreserved Characters

#### checks alphanumeric

1. expect is unreserved
2. expect is unreserved
3. expect is unreserved
4. expect is unreserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_unreserved("A")
expect is_unreserved("z")
expect is_unreserved("0")
expect is_unreserved("9")
```

</details>

#### checks special allowed chars

1. expect is unreserved
2. expect is unreserved
3. expect is unreserved
4. expect is unreserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_unreserved("-")
expect is_unreserved(".")
expect is_unreserved("_")
expect is_unreserved("~")
```

</details>

#### checks reserved chars

1. expect not is unreserved
2. expect not is unreserved
3. expect not is unreserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not is_unreserved("!")
expect not is_unreserved("@")
expect not is_unreserved(" ")
```

</details>

### Round-trip

#### parse and build URL

1. expect rebuilt contains
2. expect rebuilt contains
3. expect rebuilt contains
4. expect rebuilt contains
5. expect rebuilt contains
6. expect rebuilt contains
7. expect rebuilt contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "https://user:pass@example.com:8080/path?key=val#frag"
match parse_url(original):
    case Some(url):
        val rebuilt = build_url(url)
        expect rebuilt.contains("https://")
        expect rebuilt.contains("user:pass@")
        expect rebuilt.contains("example.com")
        expect rebuilt.contains(":8080")
        expect rebuilt.contains("/path")
        expect rebuilt.contains("?key=val")
        expect rebuilt.contains("#frag")
    case nil: expect false
```

</details>

#### parse and build query string

1. expect rebuilt contains
2. expect rebuilt contains
3. expect rebuilt contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "a=1&b=2&c=3"
val params = parse_query_string(original)
val rebuilt = build_query_string(params)
expect rebuilt.contains("a=1")
expect rebuilt.contains("b=2")
expect rebuilt.contains("c=3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/url_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- URL Utilities
- URL Encoding
- URL Decoding
- Character Codes
- Hex Conversion
- URL Parsing
- URL Building
- Query String
- URL Validation
- URL Operations
- Integer Parsing
- Unreserved Characters
- Round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
