# URL parser truth table

> Absolute expected values for `nogc_sync_mut.http_client.types.parse_url`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 68 | 68 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# URL parser truth table

Absolute expected values for `nogc_sync_mut.http_client.types.parse_url`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #URLPARSE |
| Category | Standard Library / Security |
| Status | Implemented |
| Source | `test/01_unit/std/http_client/url_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Absolute expected values for `nogc_sync_mut.http_client.types.parse_url`.

The parser is **fail-closed**: anything that is not an absolute URL yields
`None`. It never guesses a scheme and never invents a host, because a lenient
default made every malformed URL mutually same-origin with every other
malformed URL.

## Scenarios

### parse_url: absolute special-scheme URLs

#### parses a bare http URL with the default port and root path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a bare http URL with the default port and root path
   - Expected: fields("http://example.com/") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("parses a bare http URL with the default port and root path")
expect(fields("http://example.com/")).to_equal("http|example.com|80|/|||-")
```

</details>

#### supplies the root path when the URL has none

- supplies the root path when the URL has none
   - Expected: fields("http://example.com") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("supplies the root path when the URL has none")
expect(fields("http://example.com")).to_equal("http|example.com|80|/|||-")
```

</details>

#### splits path, query and fragment

- splits path, query and fragment
   - Expected: fields("https://example.com/a/b?c=d#e") equals `https|example.com|443|/a/b|c=d|e|-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("splits path, query and fragment")
expect(fields("https://example.com/a/b?c=d#e")).to_equal("https|example.com|443|/a/b|c=d|e|-")
```

</details>

#### keeps an explicit non-default port

- keeps an explicit non-default port
   - Expected: fields("http://example.com:8080/p") equals `http|example.com|8080|/p|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("keeps an explicit non-default port")
expect(fields("http://example.com:8080/p")).to_equal("http|example.com|8080|/p|||-")
```

</details>

#### keeps an explicit default http port

- keeps an explicit default http port
   - Expected: fields("http://example.com:80/") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("keeps an explicit default http port")
expect(fields("http://example.com:80/")).to_equal("http|example.com|80|/|||-")
```

</details>

#### keeps an explicit default https port

- keeps an explicit default https port
   - Expected: fields("https://example.com:443/") equals `https|example.com|443|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("keeps an explicit default https port")
expect(fields("https://example.com:443/")).to_equal("https|example.com|443|/|||-")
```

</details>

#### treats an empty port as no port

- treats an empty port as no port
   - Expected: fields("http://example.com:/x") equals `http|example.com|80|/x|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("treats an empty port as no port")
expect(fields("http://example.com:/x")).to_equal("http|example.com|80|/x|||-")
```

</details>

#### parses a query with no path

- parses a query with no path
   - Expected: fields("https://example.com?q=1") equals `https|example.com|443|/|q=1||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("parses a query with no path")
expect(fields("https://example.com?q=1")).to_equal("https|example.com|443|/|q=1||-")
```

</details>

#### parses a fragment with no path

- parses a fragment with no path
   - Expected: fields("https://example.com#f") equals `https|example.com|443|/||f|-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("parses a fragment with no path")
expect(fields("https://example.com#f")).to_equal("https|example.com|443|/||f|-")
```

</details>

### parse_url: the other special schemes

#### gives ws the http default port

- gives ws the http default port
   - Expected: fields("ws://example.com/s") equals `ws|example.com|80|/s|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives ws the http default port")
expect(fields("ws://example.com/s")).to_equal("ws|example.com|80|/s|||-")
```

</details>

#### gives wss the https default port

- gives wss the https default port
   - Expected: fields("wss://example.com/s") equals `wss|example.com|443|/s|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives wss the https default port")
expect(fields("wss://example.com/s")).to_equal("wss|example.com|443|/s|||-")
```

</details>

#### gives ftp port 21

- gives ftp port 21
   - Expected: fields("ftp://example.com/f") equals `ftp|example.com|21|/f|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives ftp port 21")
expect(fields("ftp://example.com/f")).to_equal("ftp|example.com|21|/f|||-")
```

</details>

#### gives file no port and an empty host

- gives file no port and an empty host
   - Expected: fields("file:///tmp/x") equals `file||0|/tmp/x|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives file no port and an empty host")
expect(fields("file:///tmp/x")).to_equal("file||0|/tmp/x|||-")
```

</details>

#### rejects a port on file:

- rejects a port on file:
   - Expected: fields("file://host:80/x") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects a port on file:")
expect(fields("file://host:80/x")).to_equal("FAIL")
```

</details>

### parse_url: non-special schemes stay themselves

#### does not turn data: into http

- does not turn data: into http
   - Expected: fields("data:text/plain,hello") equals `data||0|text/plain,hello|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("does not turn data: into http")
expect(fields("data:text/plain,hello")).to_equal("data||0|text/plain,hello|||opaque")
```

</details>

#### does not turn about: into http

- does not turn about: into http
   - Expected: fields("about:blank") equals `about||0|blank|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("does not turn about: into http")
expect(fields("about:blank")).to_equal("about||0|blank|||opaque")
```

</details>

#### does not turn javascript: into http

- does not turn javascript: into http
   - Expected: fields("javascript:alert(1)") equals `javascript||0|alert(1)|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("does not turn javascript: into http")
expect(fields("javascript:alert(1)")).to_equal("javascript||0|alert(1)|||opaque")
```

</details>

#### does not turn mailto: into http

- does not turn mailto: into http
   - Expected: fields("mailto:a@b.com") equals `mailto||0|a@b.com|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("does not turn mailto: into http")
expect(fields("mailto:a@b.com")).to_equal("mailto||0|a@b.com|||opaque")
```

</details>

#### gives every opaque URL an empty host so none are same-origin with a site

- gives every opaque URL an empty host so none are same-origin with a site
   - Expected: fields("data:text/plain,x") contains `||0|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives every opaque URL an empty host so none are same-origin with a site")
expect(fields("data:text/plain,x").contains("||0|")).to_equal(true)
```

</details>

### parse_url: normalization

#### lowercases the scheme and the host

- lowercases the scheme and the host
   - Expected: fields("HTTP://EXAMPLE.COM/P") equals `http|example.com|80|/P|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("lowercases the scheme and the host")
expect(fields("HTTP://EXAMPLE.COM/P")).to_equal("http|example.com|80|/P|||-")
```

</details>

#### preserves a trailing dot in the host (a distinct WHATWG origin)

- preserves a trailing dot in the host (a distinct WHATWG origin)
   - Expected: fields("http://example.com./") equals `http|example.com.|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("preserves a trailing dot in the host (a distinct WHATWG origin)")
expect(fields("http://example.com./")).to_equal("http|example.com.|80|/|||-")
```

</details>

#### strips surrounding whitespace

- strips surrounding whitespace
   - Expected: fields("  https://example.com/  ") equals `https|example.com|443|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("strips surrounding whitespace")
expect(fields("  https://example.com/  ")).to_equal("https|example.com|443|/|||-")
```

</details>

#### strips embedded tab and newline characters

- strips embedded tab and newline characters
   - Expected: fields("http://exa\tmple.com/") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("strips embedded tab and newline characters")
expect(fields("http://exa\tmple.com/")).to_equal("http|example.com|80|/|||-")
```

</details>

### parse_url: authority edge cases

#### takes the host after the LAST @, not the first (spoof defence)

- takes the host after the LAST @, not the first (spoof defence)
   - Expected: fields("http://user:pw@example.com/p") equals `http|example.com|80|/p|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("takes the host after the LAST @, not the first (spoof defence)")
expect(fields("http://user:pw@example.com/p")).to_equal("http|example.com|80|/p|||-")
```

</details>

#### does not let userinfo impersonate the host

- does not let userinfo impersonate the host
   - Expected: fields("http://good.com@evil.com/") equals `http|evil.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("does not let userinfo impersonate the host")
expect(fields("http://good.com@evil.com/")).to_equal("http|evil.com|80|/|||-")
```

</details>

#### keeps an IPv6 literal in brackets with its port

- keeps an IPv6 literal in brackets with its port
   - Expected: fields("http://[::1]:8080/") equals `http|[::1]|8080|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("keeps an IPv6 literal in brackets with its port")
expect(fields("http://[::1]:8080/")).to_equal("http|[::1]|8080|/|||-")
```

</details>

#### keeps an IPv6 literal with the default port

- keeps an IPv6 literal with the default port
   - Expected: fields("http://[::1]/") equals `http|[::1]|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("keeps an IPv6 literal with the default port")
expect(fields("http://[::1]/")).to_equal("http|[::1]|80|/|||-")
```

</details>

#### lowercases an IPv6 literal

- lowercases an IPv6 literal
   - Expected: fields("http://[FE80::1]/") equals `http|[fe80::1]|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("lowercases an IPv6 literal")
expect(fields("http://[FE80::1]/")).to_equal("http|[fe80::1]|80|/|||-")
```

</details>

#### rejects an unterminated IPv6 literal

- rejects an unterminated IPv6 literal
   - Expected: fields("http://[::1/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects an unterminated IPv6 literal")
expect(fields("http://[::1/")).to_equal("FAIL")
```

</details>

#### accepts structurally valid compressed and IPv4-embedded IPv6

- accepts structurally valid compressed and IPv4-embedded IPv6
   - Expected: fields("https://[::]/") equals `https|[::]|443|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("accepts structurally valid compressed and IPv4-embedded IPv6")
expect(fields("https://[::]/")).to_equal("https|[::]|443|/|||-")
expect(fields("https://[1:2:3:4:5:6:7:8]/")).to_equal(
    "https|[1:2:3:4:5:6:7:8]|443|/|||-"
)
expect(fields("https://[::ffff:192.0.2.1]/")).to_equal(
    "https|[::ffff:192.0.2.1]|443|/|||-"
)
```

</details>

#### rejects malformed IPv6 before HTTPS transport identity use

- rejects malformed IPv6 before HTTPS transport identity use
   - Expected: fields("https://[1:2:3:4:5:6:7:8:9]/") equals `FAIL`
   - Expected: fields("https://[1:2:3:4:5:6:7:10000]/") equals `FAIL`
   - Expected: fields("https://[1::2::3]/") equals `FAIL`
   - Expected: fields("https://[::ffff:192.0.2.999]/") equals `FAIL`
   - Expected: fields("https://[1:2:3:4:5:6:192.0.2.1:7]/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects malformed IPv6 before HTTPS transport identity use")
expect(fields("https://[1:2:3:4:5:6:7:8:9]/")).to_equal("FAIL")
expect(fields("https://[1:2:3:4:5:6:7:10000]/")).to_equal("FAIL")
expect(fields("https://[1::2::3]/")).to_equal("FAIL")
expect(fields("https://[::ffff:192.0.2.999]/")).to_equal("FAIL")
expect(fields("https://[1:2:3:4:5:6:192.0.2.1:7]/")).to_equal("FAIL")
```

</details>

### parse_url: fail-closed rejections

#### rejects the empty string

- rejects the empty string
   - Expected: fields("") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects the empty string")
expect(fields("")).to_equal("FAIL")
```

</details>

#### rejects whitespace-only input

- rejects whitespace-only input
   - Expected: fields("   ") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects whitespace-only input")
expect(fields("   ")).to_equal("FAIL")
```

</details>

#### rejects plainly malformed input

- rejects plainly malformed input
   - Expected: fields("not a url") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects plainly malformed input")
expect(fields("not a url")).to_equal("FAIL")
```

</details>

#### no longer makes two malformed inputs mutually same-origin

- no longer makes two malformed inputs mutually same-origin
   - Expected: fields("") == fields("not a url") and fields("") == "FAIL" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("no longer makes two malformed inputs mutually same-origin")
expect(fields("") == fields("not a url") and fields("") == "FAIL").to_equal(true)
```

</details>

#### rejects a non-numeric port instead of leaking an Option

- rejects a non-numeric port instead of leaking an Option
   - Expected: fields("http://example.com:abc/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects a non-numeric port instead of leaking an Option")
expect(fields("http://example.com:abc/")).to_equal("FAIL")
```

</details>

#### rejects an out-of-range port

- rejects an out-of-range port
   - Expected: fields("http://example.com:99999/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects an out-of-range port")
expect(fields("http://example.com:99999/")).to_equal("FAIL")
```

</details>

#### rejects port 0

- rejects port 0
   - Expected: fields("http://example.com:0/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects port 0")
expect(fields("http://example.com:0/")).to_equal("FAIL")
```

</details>

#### rejects a protocol-relative URL (no scheme to trust)

- rejects a protocol-relative URL (no scheme to trust)
   - Expected: fields("//example.com/p") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects a protocol-relative URL (no scheme to trust)")
expect(fields("//example.com/p")).to_equal("FAIL")
```

</details>

#### rejects an empty host on a special scheme

- rejects an empty host on a special scheme
   - Expected: fields("http://:8080/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects an empty host on a special scheme")
expect(fields("http://:8080/")).to_equal("FAIL")
```

</details>

#### rejects a special scheme with no authority

- rejects a special scheme with no authority
   - Expected: fields("http:example.com/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects a special scheme with no authority")
expect(fields("http:example.com/")).to_equal("FAIL")
```

</details>

#### rejects a scheme that does not start with a letter

- rejects a scheme that does not start with a letter
   - Expected: fields("1http://example.com/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects a scheme that does not start with a letter")
expect(fields("1http://example.com/")).to_equal("FAIL")
```

</details>

#### rejects a host containing a forbidden code point

- rejects a host containing a forbidden code point
   - Expected: fields("http://exa|mple.com/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("rejects a host containing a forbidden code point")
expect(fields("http://exa|mple.com/")).to_equal("FAIL")
```

</details>

### parse_url: the port is a real i64, never an Option

#### yields an arithmetic-usable port for an explicit port

- yields an arithmetic-usable port for an explicit port
   - Expected: port_of("http://example.com:8080/") + 1 equals `8081`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("yields an arithmetic-usable port for an explicit port")
expect(port_of("http://example.com:8080/") + 1).to_equal(8081)
```

</details>

#### yields an arithmetic-usable port for a default port

- yields an arithmetic-usable port for a default port
   - Expected: port_of("https://example.com/") + 1 equals `444`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("yields an arithmetic-usable port for a default port")
expect(port_of("https://example.com/") + 1).to_equal(444)
```

</details>

#### yields 0, not garbage, for a scheme with no default port

- yields 0, not garbage, for a scheme with no default port
   - Expected: port_of("data:x") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("yields 0, not garbage, for a scheme with no default port")
expect(port_of("data:x")).to_equal(0)
```

</details>

#### yields 0 for file, which has no default port

- yields 0 for file, which has no default port
   - Expected: port_of("file:///tmp/x") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("yields 0 for file, which has no default port")
expect(port_of("file:///tmp/x")).to_equal(0)
```

</details>

### url_default_port and url_is_special

#### knows the http default port

- knows the http default port
   - Expected: url_default_port("http") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("knows the http default port")
expect(url_default_port("http")).to_equal(80)
```

</details>

#### knows the https default port

- knows the https default port
   - Expected: url_default_port("https") equals `443`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("knows the https default port")
expect(url_default_port("https")).to_equal(443)
```

</details>

#### knows the ws default port

- knows the ws default port
   - Expected: url_default_port("ws") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("knows the ws default port")
expect(url_default_port("ws")).to_equal(80)
```

</details>

#### knows the wss default port

- knows the wss default port
   - Expected: url_default_port("wss") equals `443`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("knows the wss default port")
expect(url_default_port("wss")).to_equal(443)
```

</details>

#### knows the ftp default port

- knows the ftp default port
   - Expected: url_default_port("ftp") equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("knows the ftp default port")
expect(url_default_port("ftp")).to_equal(21)
```

</details>

#### gives file no default port

- gives file no default port
   - Expected: url_default_port("file") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives file no default port")
expect(url_default_port("file")).to_equal(0)
```

</details>

#### gives a non-special scheme no default port

- gives a non-special scheme no default port
   - Expected: url_default_port("data") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("gives a non-special scheme no default port")
expect(url_default_port("data")).to_equal(0)
```

</details>

#### treats http as special

- treats http as special
   - Expected: url_is_special("http") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("treats http as special")
expect(url_is_special("http")).to_equal(true)
```

</details>

#### treats file as special

- treats file as special
   - Expected: url_is_special("file") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("treats file as special")
expect(url_is_special("file")).to_equal(true)
```

</details>

#### does not treat data as special

- does not treat data as special
   - Expected: url_is_special("data") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("does not treat data as special")
expect(url_is_special("data")).to_equal(false)
```

</details>

### url helpers propagate the failure

#### round-trips a URL through build_url

- round-trips a URL through build_url
   - Expected: build_url("https", "example.com", 443, "/a", "", "") equals `https://example.com/a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("round-trips a URL through build_url")
expect(build_url("https", "example.com", 443, "/a", "", "")).to_equal("https://example.com/a")
```

</details>

#### emits a non-default port in build_url

- emits a non-default port in build_url
   - Expected: build_url("http", "example.com", 8080, "/a", "", "") equals `http://example.com:8080/a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("emits a non-default port in build_url")
expect(build_url("http", "example.com", 8080, "/a", "", "")).to_equal("http://example.com:8080/a")
```

</details>

#### joins a relative path onto a base

- joins a relative path onto a base
   - Expected: joined("http://example.com/a/b", "c") equals `http://example.com/a/c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("joins a relative path onto a base")
expect(joined("http://example.com/a/b", "c")).to_equal("http://example.com/a/c")
```

</details>

#### returns an absolute relative unchanged

- returns an absolute relative unchanged
   - Expected: joined("http://example.com/a", "https://other.com/x") equals `https://other.com/x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("returns an absolute relative unchanged")
expect(joined("http://example.com/a", "https://other.com/x")).to_equal("https://other.com/x")
```

</details>

#### fails the join when the base is unparseable

- fails the join when the base is unparseable
   - Expected: joined("not a url", "c") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("fails the join when the base is unparseable")
expect(joined("not a url", "c")).to_equal("FAIL")
```

</details>

#### fails the join when the base is opaque

- fails the join when the base is opaque
   - Expected: joined("data:text/plain,x", "c") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("fails the join when the base is opaque")
expect(joined("data:text/plain,x", "c")).to_equal("FAIL")
```

</details>

#### adds a query param

- adds a query param
   - Expected: added("http://example.com/p", "k", "v") equals `http://example.com/p?k=v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("adds a query param")
expect(added("http://example.com/p", "k", "v")).to_equal("http://example.com/p?k=v")
```

</details>

#### fails add_query_param on an unparseable URL

- fails add_query_param on an unparseable URL
   - Expected: added("not a url", "k", "v") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("fails add_query_param on an unparseable URL")
expect(added("not a url", "k", "v")).to_equal("FAIL")
```

</details>

#### fails add_query_param on an opaque URL

- fails add_query_param on an opaque URL
   - Expected: added("data:text/plain,x", "k", "v") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("fails add_query_param on an opaque URL")
expect(added("data:text/plain,x", "k", "v")).to_equal("FAIL")
```

</details>

#### removes a query param

- removes a query param
   - Expected: removed("http://example.com/p?k=v&j=w", "k") equals `http://example.com/p?j=w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("removes a query param")
expect(removed("http://example.com/p?k=v&j=w", "k")).to_equal("http://example.com/p?j=w")
```

</details>

#### fails remove_query_param on an unparseable URL

- fails remove_query_param on an unparseable URL
   - Expected: removed("", "k") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("fails remove_query_param on an unparseable URL")
expect(removed("", "k")).to_equal("FAIL")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 68 |
| Active scenarios | 68 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-STD`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `484430c0c1820ed76de9da57757f3c5d32d344a3e3b855ab724a3b1cf30e042d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `484430c0c1820ed76de9da57757f3c5d32d344a3e3b855ab724a3b1cf30e042d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `484430c0c1820ed76de9da57757f3c5d32d344a3e3b855ab724a3b1cf30e042d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/std/http_client/url_parse_spec.spl
mirror: doc/06_spec/01_unit/std/http_client/url_parse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/http_client/url_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/http_client/url_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/http_client/url_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/std/http_client/url_parse_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a bare http URL with the default port and root path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/http_client/url_parse_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supplies the root path when the URL has none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/http_client/url_parse_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits path, query and fragment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
