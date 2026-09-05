# Url Utils Specification

> Tests covering URL Utilities, URL Encoding, URL Decoding, Character Codes, Hex Conversion, URL Parsing, URL Building, Query String, URL Validation, URL Operations, Integer Parsing, Unreserved Characters, Round-trip.

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

- encodes simple string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes simple string")
expect url_encode("hello") == "hello"
```

</details>

#### encodes space

- encodes space


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes space")
val result = url_encode("hello world")
expect result.contains("%20")
```

</details>

#### encodes special chars

- encodes special chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes special chars")
val result = url_encode("a+b")
expect result.contains("%")
```

</details>

### URL Decoding

#### decodes simple string

- decodes simple string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes simple string")
expect url_decode("hello") == "hello"
```

</details>

#### decodes percent-encoded space

- decodes percent-encoded space


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes percent-encoded space")
expect url_decode("hello%20world") == "hello world"
```

</details>

#### decodes plus as space

- decodes plus as space


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes plus as space")
expect url_decode("hello+world") == "hello world"
```

</details>

#### round-trip encode/decode

- round-trip encode/decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip encode/decode")
val original = "hello world"
val encoded = url_encode(original)
val decoded = url_decode(encoded)
expect decoded == original
```

</details>

### Character Codes

#### gets char code for letters

- gets char code for letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets char code for letters")
expect char_code("A") == 65
expect char_code("a") == 97
expect char_code("Z") == 90
expect char_code("z") == 122
```

</details>

#### gets char code for digits

- gets char code for digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets char code for digits")
expect char_code("0") == 48
expect char_code("9") == 57
```

</details>

#### converts from char code

- converts from char code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts from char code")
expect from_char_code(65) == "A"
expect from_char_code(97) == "a"
expect from_char_code(48) == "0"
```

</details>

#### round-trip char code

- round-trip char code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip char code")
val code = char_code("A")
val ch = from_char_code(code)
expect ch == "A"
```

</details>

### Hex Conversion

#### converts to hex

- converts to hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to hex")
expect to_hex(0) == "00"
expect to_hex(15) == "0F"
expect to_hex(255) == "FF"
```

</details>

#### converts hex digit

- converts hex digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts hex digit")
expect hex_digit(0) == "0"
expect hex_digit(9) == "9"
expect hex_digit(10) == "A"
expect hex_digit(15) == "F"
```

</details>

#### parses valid hex

- parses valid hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses valid hex")
match from_hex("00"):
    case Some(n): expect n == 0
    case nil: expect false
match from_hex("FF"):
    case Some(n): expect n == 255
    case nil: expect false
```

</details>

#### returns nil for invalid hex

- returns nil for invalid hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for invalid hex")
match from_hex("GG"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### parses hex digit value

- parses hex digit value


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses hex digit value")
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

- parses simple URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple URL")
match parse_url("http://example.com"):
    case Some(url):
        expect url.scheme == "http"
        expect url.host == "example.com"
        expect url.path == "/"
    case nil: expect false
```

</details>

#### parses URL with path

- parses URL with path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL with path")
match parse_url("https://example.com/path/to/resource"):
    case Some(url):
        expect url.scheme == "https"
        expect url.host == "example.com"
        expect url.path == "/path/to/resource"
    case nil: expect false
```

</details>

#### parses URL with port

- parses URL with port


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL with port")
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

- parses URL with query


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL with query")
match parse_url("http://example.com/path?key=value"):
    case Some(url):
        expect url.path == "/path"
        expect url.query == "key=value"
    case nil: expect false
```

</details>

#### parses URL with fragment

- parses URL with fragment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL with fragment")
match parse_url("http://example.com/page#section"):
    case Some(url):
        expect url.path == "/page"
        expect url.fragment == "section"
    case nil: expect false
```

</details>

#### parses URL with username

- parses URL with username


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL with username")
match parse_url("http://user@example.com/"):
    case Some(url):
        expect url.username == "user"
        expect url.host == "example.com"
    case nil: expect false
```

</details>

#### parses URL with credentials

- parses URL with credentials


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses URL with credentials")
match parse_url("ftp://user:pass@example.com/"):
    case Some(url):
        expect url.username == "user"
        expect url.password == "pass"
        expect url.host == "example.com"
    case nil: expect false
```

</details>

#### parses complete URL

- parses complete URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses complete URL")
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

- returns nil for invalid URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for invalid URL")
match parse_url("not-a-url"):
    case Some(_): expect false
    case nil: expect true
```

</details>

### URL Building

#### builds simple URL

- builds simple URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds simple URL")
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

- builds URL with port


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds URL with port")
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

- omits default port


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits default port")
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

- builds URL with query


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds URL with query")
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

- checks default port


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks default port")
expect is_default_port("http", 80)
expect is_default_port("https", 443)
expect is_default_port("ftp", 21)
expect not is_default_port("http", 8080)
```

</details>

### Query String

#### parses simple query

- parses simple query


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple query")
val params = parse_query_string("key=value")
expect params.len() == 1
expect params[0].0 == "key"
expect params[0].1 == "value"
```

</details>

#### parses multiple params

- parses multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple params")
val params = parse_query_string("a=1&b=2&c=3")
expect params.len() == 3
expect params[0].0 == "a"
expect params[1].0 == "b"
expect params[2].0 == "c"
```

</details>

#### parses empty value

- parses empty value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty value")
val params = parse_query_string("key=")
expect params.len() == 1
expect params[0].0 == "key"
expect params[0].1 == ""
```

</details>

#### parses no value

- parses no value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses no value")
val params = parse_query_string("flag")
expect params.len() == 1
expect params[0].0 == "flag"
expect params[0].1 == ""
```

</details>

#### parses empty string

- parses empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty string")
val params = parse_query_string("")
expect params.len() == 0
```

</details>

#### builds simple query

- builds simple query


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds simple query")
val params = [("key", "value")]
val result = build_query_string(params)
expect result == "key=value"
```

</details>

#### builds multiple params

- builds multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds multiple params")
val params = [("a", "1"), ("b", "2"), ("c", "3")]
val result = build_query_string(params)
expect result.contains("a=1")
expect result.contains("b=2")
expect result.contains("c=3")
expect result.contains("&")
```

</details>

#### builds with encoding

- builds with encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with encoding")
val params = [("key", "hello world")]
val result = build_query_string(params)
expect result.contains("%20")
```

</details>

#### adds param to empty query

- adds param to empty query


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds param to empty query")
val result = add_query_param(query="", key="key", value="value")
expect result == "key=value"
```

</details>

#### adds param to existing query

- adds param to existing query


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds param to existing query")
val result = add_query_param(query="a=1", key="b", value="2")
expect result.contains("a=1")
expect result.contains("b=2")
expect result.contains("&")
```

</details>

### URL Validation

#### validates valid URLs

- validates valid URLs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates valid URLs")
expect is_valid_url("http://example.com")
expect is_valid_url("https://example.com/path")
expect is_valid_url("ftp://files.example.com")
```

</details>

#### rejects invalid URLs

- rejects invalid URLs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid URLs")
expect not is_valid_url("example.com")
expect not is_valid_url("/path/to/file")
expect not is_valid_url("http:example.com")
```

</details>

#### checks absolute URL

- checks absolute URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks absolute URL")
expect is_absolute_url("http://example.com")
expect is_absolute_url("https://example.com/path")
expect not is_absolute_url("/path/to/file")
expect not is_absolute_url("relative/path")
```

</details>

#### checks relative URL

- checks relative URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks relative URL")
expect is_relative_url("/path/to/file")
expect is_relative_url("relative/path")
expect not is_relative_url("http://example.com")
```

</details>

### URL Operations

#### gets base URL

- gets base URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets base URL")
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

- gets base URL with port


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets base URL with port")
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

- gets full path


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets full path")
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

- joins absolute URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins absolute URL")
val result = join_url(base="http://example.com", rel="https://other.com/path")
expect result == "https://other.com/path"
```

</details>

#### joins relative URL with slash

- joins relative URL with slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins relative URL with slash")
val result = join_url(base="http://example.com/", rel="/path")
expect result == "http://example.com/path"
```

</details>

#### joins relative URL without slash

- joins relative URL without slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins relative URL without slash")
val result = join_url(base="http://example.com", rel="path")
expect result == "http://example.com/path"
```

</details>

#### joins both slashes

- joins both slashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins both slashes")
val result = join_url(base="http://example.com/", rel="/path")
expect not result.contains("//path")
```

</details>

### Integer Parsing

#### parses valid int

- parses valid int


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses valid int")
match parse_int("123"):
    case Some(n): expect n == 123
    case nil: expect false
```

</details>

#### parses zero

- parses zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
match parse_int("0"):
    case Some(n): expect n == 0
    case nil: expect false
```

</details>

#### returns nil for invalid

- returns nil for invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for invalid")
match parse_int("abc"):
    case Some(_): expect false
    case nil: expect true
```

</details>

#### returns nil for empty

- returns nil for empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty")
match parse_int(""):
    case Some(_): expect false
    case nil: expect true
```

</details>

### Unreserved Characters

#### checks alphanumeric

- checks alphanumeric


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks alphanumeric")
expect is_unreserved("A")
expect is_unreserved("z")
expect is_unreserved("0")
expect is_unreserved("9")
```

</details>

#### checks special allowed chars

- checks special allowed chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks special allowed chars")
expect is_unreserved("-")
expect is_unreserved(".")
expect is_unreserved("_")
expect is_unreserved("~")
```

</details>

#### checks reserved chars

- checks reserved chars


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks reserved chars")
expect not is_unreserved("!")
expect not is_unreserved("@")
expect not is_unreserved(" ")
```

</details>

### Round-trip

#### parse and build URL

- parse and build URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse and build URL")
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

- parse and build query string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse and build query string")
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
| Source | `test/unit/app/tooling/url_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering URL Utilities, URL Encoding, URL Decoding, Character Codes, Hex Conversion, URL Parsing, URL Building, Query String, URL Validation, URL Operations, Integer Parsing, Unreserved Characters, Round-trip.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efb9684224af43318f4463d056428fdd28558f5b63ac6e243eec8c3bbd471b10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efb9684224af43318f4463d056428fdd28558f5b63ac6e243eec8c3bbd471b10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efb9684224af43318f4463d056428fdd28558f5b63ac6e243eec8c3bbd471b10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/url_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/url_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/url_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/url_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/url_utils_spec.spl:367:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes simple string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/url_utils_spec.spl:372:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/url_utils_spec.spl:378:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes special chars' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
