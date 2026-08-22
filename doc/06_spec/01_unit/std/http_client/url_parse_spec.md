# URL parser truth table

> Verifies the url parse behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 68 | 68 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# URL parser truth table

Verifies the url parse behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #URLPARSE |
| Category | Standard Library / Security |
| Status | Implemented |
| Source | `test/01_unit/std/http_client/url_parse_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the url parse behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### parse_url: absolute special-scheme URLs

#### parses a bare http URL with the default port and root path

- Verify: parses a bare http URL with the default port and root path
   - Expected: fields("http://example.com/") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: parses a bare http URL with the default port and root path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com/")).to_equal("http|example.com|80|/|||-")
```

</details>

#### supplies the root path when the URL has none

- Verify: supplies the root path when the URL has none
   - Expected: fields("http://example.com") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: supplies the root path when the URL has none")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com")).to_equal("http|example.com|80|/|||-")
```

</details>

#### splits path, query and fragment

- Verify: splits path, query and fragment
   - Expected: fields("https://example.com/a/b?c=d#e") equals `https|example.com|443|/a/b|c=d|e|-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: splits path, query and fragment")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("https://example.com/a/b?c=d#e")).to_equal("https|example.com|443|/a/b|c=d|e|-")
```

</details>

#### keeps an explicit non-default port

- Verify: keeps an explicit non-default port
   - Expected: fields("http://example.com:8080/p") equals `http|example.com|8080|/p|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: keeps an explicit non-default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com:8080/p")).to_equal("http|example.com|8080|/p|||-")
```

</details>

#### keeps an explicit default http port

- Verify: keeps an explicit default http port
   - Expected: fields("http://example.com:80/") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: keeps an explicit default http port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com:80/")).to_equal("http|example.com|80|/|||-")
```

</details>

#### keeps an explicit default https port

- Verify: keeps an explicit default https port
   - Expected: fields("https://example.com:443/") equals `https|example.com|443|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: keeps an explicit default https port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("https://example.com:443/")).to_equal("https|example.com|443|/|||-")
```

</details>

#### treats an empty port as no port

- Verify: treats an empty port as no port
   - Expected: fields("http://example.com:/x") equals `http|example.com|80|/x|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: treats an empty port as no port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com:/x")).to_equal("http|example.com|80|/x|||-")
```

</details>

#### parses a query with no path

- Verify: parses a query with no path
   - Expected: fields("https://example.com?q=1") equals `https|example.com|443|/|q=1||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: parses a query with no path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("https://example.com?q=1")).to_equal("https|example.com|443|/|q=1||-")
```

</details>

#### parses a fragment with no path

- Verify: parses a fragment with no path
   - Expected: fields("https://example.com#f") equals `https|example.com|443|/||f|-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: parses a fragment with no path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("https://example.com#f")).to_equal("https|example.com|443|/||f|-")
```

</details>

### parse_url: the other special schemes

#### gives ws the http default port

- Verify: gives ws the http default port
   - Expected: fields("ws://example.com/s") equals `ws|example.com|80|/s|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives ws the http default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("ws://example.com/s")).to_equal("ws|example.com|80|/s|||-")
```

</details>

#### gives wss the https default port

- Verify: gives wss the https default port
   - Expected: fields("wss://example.com/s") equals `wss|example.com|443|/s|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives wss the https default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("wss://example.com/s")).to_equal("wss|example.com|443|/s|||-")
```

</details>

#### gives ftp port 21

- Verify: gives ftp port 21
   - Expected: fields("ftp://example.com/f") equals `ftp|example.com|21|/f|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives ftp port 21")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("ftp://example.com/f")).to_equal("ftp|example.com|21|/f|||-")
```

</details>

#### gives file no port and an empty host

- Verify: gives file no port and an empty host
   - Expected: fields("file:///tmp/x") equals `file||0|/tmp/x|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives file no port and an empty host")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("file:///tmp/x")).to_equal("file||0|/tmp/x|||-")
```

</details>

#### rejects a port on file:

- Verify: rejects a port on file:
   - Expected: fields("file://host:80/x") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects a port on file:")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("file://host:80/x")).to_equal("FAIL")
```

</details>

### parse_url: non-special schemes stay themselves

#### does not turn data: into http

- Verify: does not turn data: into http
   - Expected: fields("data:text/plain,hello") equals `data||0|text/plain,hello|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: does not turn data: into http")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("data:text/plain,hello")).to_equal("data||0|text/plain,hello|||opaque")
```

</details>

#### does not turn about: into http

- Verify: does not turn about: into http
   - Expected: fields("about:blank") equals `about||0|blank|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: does not turn about: into http")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("about:blank")).to_equal("about||0|blank|||opaque")
```

</details>

#### does not turn javascript: into http

- Verify: does not turn javascript: into http
   - Expected: fields("javascript:alert(1)") equals `javascript||0|alert(1)|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: does not turn javascript: into http")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("javascript:alert(1)")).to_equal("javascript||0|alert(1)|||opaque")
```

</details>

#### does not turn mailto: into http

- Verify: does not turn mailto: into http
   - Expected: fields("mailto:a@b.com") equals `mailto||0|a@b.com|||opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: does not turn mailto: into http")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("mailto:a@b.com")).to_equal("mailto||0|a@b.com|||opaque")
```

</details>

#### gives every opaque URL an empty host so none are same-origin with a site

- Verify: gives every opaque URL an empty host so none are same-origin with a site
   - Expected: fields("data:text/plain,x") contains `||0|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives every opaque URL an empty host so none are same-origin with a site")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("data:text/plain,x").contains("||0|")).to_equal(true)
```

</details>

### parse_url: normalization

#### lowercases the scheme and the host

- Verify: lowercases the scheme and the host
   - Expected: fields("HTTP://EXAMPLE.COM/P") equals `http|example.com|80|/P|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: lowercases the scheme and the host")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("HTTP://EXAMPLE.COM/P")).to_equal("http|example.com|80|/P|||-")
```

</details>

#### preserves a trailing dot in the host (a distinct WHATWG origin)

- Verify: preserves a trailing dot in the host (a distinct WHATWG origin)
   - Expected: fields("http://example.com./") equals `http|example.com.|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: preserves a trailing dot in the host (a distinct WHATWG origin)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com./")).to_equal("http|example.com.|80|/|||-")
```

</details>

#### strips surrounding whitespace

- Verify: strips surrounding whitespace
   - Expected: fields("  https://example.com/  ") equals `https|example.com|443|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: strips surrounding whitespace")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("  https://example.com/  ")).to_equal("https|example.com|443|/|||-")
```

</details>

#### strips embedded tab and newline characters

- Verify: strips embedded tab and newline characters
   - Expected: fields("http://exa\tmple.com/") equals `http|example.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: strips embedded tab and newline characters")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://exa\tmple.com/")).to_equal("http|example.com|80|/|||-")
```

</details>

### parse_url: authority edge cases

#### takes the host after the LAST @, not the first (spoof defence)

- Verify: takes the host after the LAST @, not the first (spoof defence)
   - Expected: fields("http://user:pw@example.com/p") equals `http|example.com|80|/p|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: takes the host after the LAST @, not the first (spoof defence)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://user:pw@example.com/p")).to_equal("http|example.com|80|/p|||-")
```

</details>

#### does not let userinfo impersonate the host

- Verify: does not let userinfo impersonate the host
   - Expected: fields("http://good.com@evil.com/") equals `http|evil.com|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: does not let userinfo impersonate the host")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://good.com@evil.com/")).to_equal("http|evil.com|80|/|||-")
```

</details>

#### keeps an IPv6 literal in brackets with its port

- Verify: keeps an IPv6 literal in brackets with its port
   - Expected: fields("http://[::1]:8080/") equals `http|[::1]|8080|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: keeps an IPv6 literal in brackets with its port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://[::1]:8080/")).to_equal("http|[::1]|8080|/|||-")
```

</details>

#### keeps an IPv6 literal with the default port

- Verify: keeps an IPv6 literal with the default port
   - Expected: fields("http://[::1]/") equals `http|[::1]|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: keeps an IPv6 literal with the default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://[::1]/")).to_equal("http|[::1]|80|/|||-")
```

</details>

#### lowercases an IPv6 literal

- Verify: lowercases an IPv6 literal
   - Expected: fields("http://[FE80::1]/") equals `http|[fe80::1]|80|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: lowercases an IPv6 literal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://[FE80::1]/")).to_equal("http|[fe80::1]|80|/|||-")
```

</details>

#### rejects an unterminated IPv6 literal

- Verify: rejects an unterminated IPv6 literal
   - Expected: fields("http://[::1/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: rejects an unterminated IPv6 literal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://[::1/")).to_equal("FAIL")
```

</details>

#### accepts structurally valid compressed and IPv4-embedded IPv6

- Verify: accepts structurally valid compressed and IPv4-embedded IPv6
   - Expected: fields("https://[::]/") equals `https|[::]|443|/|||-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: accepts structurally valid compressed and IPv4-embedded IPv6")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects malformed IPv6 before HTTPS transport identity use
   - Expected: fields("https://[1:2:3:4:5:6:7:8:9]/") equals `FAIL`
   - Expected: fields("https://[1:2:3:4:5:6:7:10000]/") equals `FAIL`
   - Expected: fields("https://[1::2::3]/") equals `FAIL`
   - Expected: fields("https://[::ffff:192.0.2.999]/") equals `FAIL`
   - Expected: fields("https://[1:2:3:4:5:6:192.0.2.1:7]/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects malformed IPv6 before HTTPS transport identity use")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("https://[1:2:3:4:5:6:7:8:9]/")).to_equal("FAIL")
expect(fields("https://[1:2:3:4:5:6:7:10000]/")).to_equal("FAIL")
expect(fields("https://[1::2::3]/")).to_equal("FAIL")
expect(fields("https://[::ffff:192.0.2.999]/")).to_equal("FAIL")
expect(fields("https://[1:2:3:4:5:6:192.0.2.1:7]/")).to_equal("FAIL")
```

</details>

### parse_url: fail-closed rejections

#### rejects the empty string

- Verify: rejects the empty string
   - Expected: fields("") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects the empty string")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("")).to_equal("FAIL")
```

</details>

#### rejects whitespace-only input

- Verify: rejects whitespace-only input
   - Expected: fields("   ") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects whitespace-only input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("   ")).to_equal("FAIL")
```

</details>

#### rejects plainly malformed input

- Verify: rejects plainly malformed input
   - Expected: fields("not a url") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects plainly malformed input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("not a url")).to_equal("FAIL")
```

</details>

#### no longer makes two malformed inputs mutually same-origin

- Verify: no longer makes two malformed inputs mutually same-origin
   - Expected: fields("") == fields("not a url") and fields("") == "FAIL" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: no longer makes two malformed inputs mutually same-origin")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("") == fields("not a url") and fields("") == "FAIL").to_equal(true)
```

</details>

#### rejects a non-numeric port instead of leaking an Option

- Verify: rejects a non-numeric port instead of leaking an Option
   - Expected: fields("http://example.com:abc/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects a non-numeric port instead of leaking an Option")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com:abc/")).to_equal("FAIL")
```

</details>

#### rejects an out-of-range port

- Verify: rejects an out-of-range port
   - Expected: fields("http://example.com:99999/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects an out-of-range port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com:99999/")).to_equal("FAIL")
```

</details>

#### rejects port 0

- Verify: rejects port 0
   - Expected: fields("http://example.com:0/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects port 0")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://example.com:0/")).to_equal("FAIL")
```

</details>

#### rejects a protocol-relative URL (no scheme to trust)

- Verify: rejects a protocol-relative URL (no scheme to trust)
   - Expected: fields("//example.com/p") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects a protocol-relative URL (no scheme to trust)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("//example.com/p")).to_equal("FAIL")
```

</details>

#### rejects an empty host on a special scheme

- Verify: rejects an empty host on a special scheme
   - Expected: fields("http://:8080/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects an empty host on a special scheme")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://:8080/")).to_equal("FAIL")
```

</details>

#### rejects a special scheme with no authority

- Verify: rejects a special scheme with no authority
   - Expected: fields("http:example.com/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects a special scheme with no authority")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http:example.com/")).to_equal("FAIL")
```

</details>

#### rejects a scheme that does not start with a letter

- Verify: rejects a scheme that does not start with a letter
   - Expected: fields("1http://example.com/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects a scheme that does not start with a letter")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("1http://example.com/")).to_equal("FAIL")
```

</details>

#### rejects a host containing a forbidden code point

- Verify: rejects a host containing a forbidden code point
   - Expected: fields("http://exa|mple.com/") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: rejects a host containing a forbidden code point")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(fields("http://exa|mple.com/")).to_equal("FAIL")
```

</details>

### parse_url: the port is a real i64, never an Option

#### yields an arithmetic-usable port for an explicit port

- Verify: yields an arithmetic-usable port for an explicit port
   - Expected: port_of("http://example.com:8080/") + 1 equals `8081)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: yields an arithmetic-usable port for an explicit port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(port_of("http://example.com:8080/") + 1).to_equal(8081)  # oracle: pinned constant asserted by this scenario
```

</details>

#### yields an arithmetic-usable port for a default port

- Verify: yields an arithmetic-usable port for a default port
   - Expected: port_of("https://example.com/") + 1 equals `444)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: yields an arithmetic-usable port for a default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(port_of("https://example.com/") + 1).to_equal(444)  # oracle: pinned constant asserted by this scenario
```

</details>

#### yields 0, not garbage, for a scheme with no default port

- Verify: yields 0, not garbage, for a scheme with no default port
   - Expected: port_of("data:x") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: yields 0, not garbage, for a scheme with no default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(port_of("data:x")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### yields 0 for file, which has no default port

- Verify: yields 0 for file, which has no default port
   - Expected: port_of("file:///tmp/x") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: yields 0 for file, which has no default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(port_of("file:///tmp/x")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### url_default_port and url_is_special

#### knows the http default port

- Verify: knows the http default port
   - Expected: url_default_port("http") equals `80)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: knows the http default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("http")).to_equal(80)  # oracle: pinned constant asserted by this scenario
```

</details>

#### knows the https default port

- Verify: knows the https default port
   - Expected: url_default_port("https") equals `443)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: knows the https default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("https")).to_equal(443)  # oracle: pinned constant asserted by this scenario
```

</details>

#### knows the ws default port

- Verify: knows the ws default port
   - Expected: url_default_port("ws") equals `80)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: knows the ws default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("ws")).to_equal(80)  # oracle: pinned constant asserted by this scenario
```

</details>

#### knows the wss default port

- Verify: knows the wss default port
   - Expected: url_default_port("wss") equals `443)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: knows the wss default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("wss")).to_equal(443)  # oracle: pinned constant asserted by this scenario
```

</details>

#### knows the ftp default port

- Verify: knows the ftp default port
   - Expected: url_default_port("ftp") equals `21)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: knows the ftp default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("ftp")).to_equal(21)  # oracle: pinned constant asserted by this scenario
```

</details>

#### gives file no default port

- Verify: gives file no default port
   - Expected: url_default_port("file") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives file no default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("file")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### gives a non-special scheme no default port

- Verify: gives a non-special scheme no default port
   - Expected: url_default_port("data") equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: gives a non-special scheme no default port")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_default_port("data")).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### treats http as special

- Verify: treats http as special
   - Expected: url_is_special("http") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: treats http as special")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_is_special("http")).to_equal(true)
```

</details>

#### treats file as special

- Verify: treats file as special
   - Expected: url_is_special("file") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: treats file as special")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_is_special("file")).to_equal(true)
```

</details>

#### does not treat data as special

- Verify: does not treat data as special
   - Expected: url_is_special("data") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: does not treat data as special")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(url_is_special("data")).to_equal(false)
```

</details>

### url helpers propagate the failure

#### round-trips a URL through build_url

- Verify: round-trips a URL through build_url
   - Expected: build_url("https", "example.com", 443, "/a", "", "") equals `https://example.com/a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: round-trips a URL through build_url")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(build_url("https", "example.com", 443, "/a", "", "")).to_equal("https://example.com/a")
```

</details>

#### emits a non-default port in build_url

- Verify: emits a non-default port in build_url
   - Expected: build_url("http", "example.com", 8080, "/a", "", "") equals `http://example.com:8080/a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: emits a non-default port in build_url")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(build_url("http", "example.com", 8080, "/a", "", "")).to_equal("http://example.com:8080/a")
```

</details>

#### joins a relative path onto a base

- Verify: joins a relative path onto a base
   - Expected: joined("http://example.com/a/b", "c") equals `http://example.com/a/c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: joins a relative path onto a base")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(joined("http://example.com/a/b", "c")).to_equal("http://example.com/a/c")
```

</details>

#### returns an absolute relative unchanged

- Verify: returns an absolute relative unchanged
   - Expected: joined("http://example.com/a", "https://other.com/x") equals `https://other.com/x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: returns an absolute relative unchanged")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(joined("http://example.com/a", "https://other.com/x")).to_equal("https://other.com/x")
```

</details>

#### fails the join when the base is unparseable

- Verify: fails the join when the base is unparseable
   - Expected: joined("not a url", "c") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: fails the join when the base is unparseable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(joined("not a url", "c")).to_equal("FAIL")
```

</details>

#### fails the join when the base is opaque

- Verify: fails the join when the base is opaque
   - Expected: joined("data:text/plain,x", "c") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: fails the join when the base is opaque")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(joined("data:text/plain,x", "c")).to_equal("FAIL")
```

</details>

#### adds a query param

- Verify: adds a query param
   - Expected: added("http://example.com/p", "k", "v") equals `http://example.com/p?k=v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: adds a query param")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(added("http://example.com/p", "k", "v")).to_equal("http://example.com/p?k=v")
```

</details>

#### fails add_query_param on an unparseable URL

- Verify: fails add_query_param on an unparseable URL
   - Expected: added("not a url", "k", "v") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: fails add_query_param on an unparseable URL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(added("not a url", "k", "v")).to_equal("FAIL")
```

</details>

#### fails add_query_param on an opaque URL

- Verify: fails add_query_param on an opaque URL
   - Expected: added("data:text/plain,x", "k", "v") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: fails add_query_param on an opaque URL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(added("data:text/plain,x", "k", "v")).to_equal("FAIL")
```

</details>

#### removes a query param

- Verify: removes a query param
   - Expected: removed("http://example.com/p?k=v&j=w", "k") equals `http://example.com/p?j=w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: removes a query param")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(removed("http://example.com/p?k=v&j=w", "k")).to_equal("http://example.com/p?j=w")
```

</details>

#### fails remove_query_param on an unparseable URL

- Verify: fails remove_query_param on an unparseable URL
   - Expected: removed("", "k") equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: fails remove_query_param on an unparseable URL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `789c41e49294761275e4be97a605a7d019fe6ccc288fd61042306a3f5a186324`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `789c41e49294761275e4be97a605a7d019fe6ccc288fd61042306a3f5a186324`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `789c41e49294761275e4be97a605a7d019fe6ccc288fd61042306a3f5a186324`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/http_client/url_parse_spec.spl
mirror: doc/06_spec/01_unit/std/http_client/url_parse_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/http_client/url_parse_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/http_client/url_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/http_client/url_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
