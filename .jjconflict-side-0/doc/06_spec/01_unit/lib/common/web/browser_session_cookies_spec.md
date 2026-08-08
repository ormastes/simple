# Browser Session Cookies Specification

> <details>

<!-- sdn-diagram:id=browser_session_cookies_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_cookies_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_cookies_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_cookies_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Cookies Specification

## Scenarios

### BrowserSession cookie helpers

#### splits and joins cookie text without dropping trailing parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_text("sid=abc; Path=/app;", ";")

expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("sid=abc")
expect(parts[1]).to_equal(" Path=/app")
expect(parts[2]).to_equal("")
expect(join_text(["sid=abc", "theme=dark"], "; ")).to_equal("sid=abc; theme=dark")
```

</details>

#### distinguishes cookie attributes from multiple document assignments

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val assignments = split_cookie_assignments("sid=abc; theme=dark; Path=/app")

expect(cookie_text_has_attributes("sid=abc; Path=/app")).to_equal(true)
expect(assignments.len()).to_equal(3)
expect(assignments[0]).to_equal("sid=abc")
expect(assignments[1]).to_equal("theme=dark")
expect(assignments[2]).to_equal("Path=/app")
```

</details>

#### parses attributes and normalizes path and domain values

- Some
   - Expected: cookie.name equals `sid`
   - Expected: cookie.value equals `abc`
   - Expected: cookie.path equals `/app`
   - Expected: cookie.domain equals `example.com`
- fail
   - Expected: normalize_cookie_path("app") equals `/app`
   - Expected: normalize_cookie_domain(".Example.com") equals `example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_cookie_line("sid=abc; Path=app; Domain=.Example.com")

match parsed:
    Some(cookie) =>
        expect(cookie.name).to_equal("sid")
        expect(cookie.value).to_equal("abc")
        expect(cookie.path).to_equal("/app")
        expect(cookie.domain).to_equal("example.com")
    nil =>
        fail("Expected parsed cookie")
expect(normalize_cookie_path("app")).to_equal("/app")
expect(normalize_cookie_domain(".Example.com")).to_equal("example.com")
```

</details>

#### upserts removes and filters cookies for request URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sid = BrowserCookie.create("sid", "abc", "/app", "example.com", false)
val theme = BrowserCookie.create("theme", "dark", "/", "", false)
val sid_updated = BrowserCookie.create("sid", "def", "/app", "example.com", false)
val sid_expired = BrowserCookie.create("sid", "gone", "/app", "example.com", true)

val jar = upsert_cookie(upsert_cookie([sid], theme), sid_updated)
val removed = upsert_cookie(jar, sid_expired)

expect(jar.len()).to_equal(2)
expect(cookie_text_for_url(jar, "https://example.com/app/page")).to_equal("sid=def; theme=dark")
expect(cookie_text_for_url(jar, "https://other.com/app/page")).to_equal("theme=dark")
expect(cookie_text_for_url(removed, "https://example.com/app/page")).to_equal("theme=dark")
expect(cookie_matches_url(sid_updated, "https://sub.example.com/app/page")).to_equal(true)
```

</details>

#### merges document cookie text and Set-Cookie style updates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jar = merge_cookie_text([], "sid=abc; theme=dark")
val scoped = merge_cookie_text(jar, "sid=def; Path=/app; Max-Age=0")

expect(jar.len()).to_equal(2)
expect(cookie_text_for_url(jar, "https://example.com/")).to_equal("sid=abc; theme=dark")
expect(scoped.len()).to_equal(2)
```

</details>

#### enforces host-only Secure and HttpOnly cookie boundaries

Confirms host-only cookies do not reach subdomains, Secure cookies do not
cross to HTTP, and HttpOnly cookies are omitted from `document.cookie`.

#### scopes cookies by hostname rather than network port

Confirms a host cookie crosses HTTPS ports but never crosses hostnames.

#### rejects foreign Domain and insecure Secure cookie updates

Confirms foreign-domain cookies and Secure cookies received over HTTP fail
closed.

#### rejects public suffix and IP Domain cookies

Confirms single-label, multi-label, private, IDNA, and IP-literal Domain
attributes fail closed while a registrable parent domain remains accepted.

#### enforces cookie prefixes SameSite None and partition isolation

Confirms `__Secure-` and `__Host-` invariants, rejects insecure
`SameSite=None`, and fails closed on unsupported partitioned cookies.

#### rejects cookie header injection

Confirms CR/LF in cookie input is rejected before storage and cannot become an
outbound request header.

#### bounds cookie size and per-domain retention

Confirms cookies over 4096 bytes are rejected and a domain retains at most 50
cookies.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_cookies_spec.spl` |
| Updated | 2026-07-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession cookie helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
