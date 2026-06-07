# Cookie Store Specification

> Verifies RFC 6265 cookie domain/path matching, SameSite enum, Set-Cookie parsing, and CookieStore storage/retrieval. No network calls — pure logic.

<!-- sdn-diagram:id=cookie_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cookie_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cookie_store_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cookie_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cookie Store Specification

Verifies RFC 6265 cookie domain/path matching, SameSite enum, Set-Cookie parsing, and CookieStore storage/retrieval. No network calls — pure logic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M16-AC6 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/browser_engine/net/cookie_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies RFC 6265 cookie domain/path matching, SameSite enum, Set-Cookie parsing,
and CookieStore storage/retrieval. No network calls — pure logic.

## Scenarios

### parse_set_cookie

#### AC-6: parses simple name=value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_simple_cookie()
expect(c.name).to_equal("session")
expect(c.value).to_equal("abc123")
```

</details>

#### AC-6: parses Domain attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_cookie_with_domain()
expect(c.domain).to_equal("example.com")
```

</details>

#### AC-6: parses Path attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_cookie_with_path()
expect(c.path).to_equal("/api")
```

</details>

#### AC-6: parses Secure flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_secure_cookie()
expect(c.secure).to_equal(true)
```

</details>

#### AC-6: parses HttpOnly flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_httponly_cookie()
expect(c.http_only).to_equal(true)
```

</details>

#### AC-6: parses SameSite=Strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_samesite_strict_cookie()
val is_strict = (c.same_site == SameSite.Strict)
expect(is_strict).to_equal(true)
```

</details>

#### AC-6: parses SameSite=Lax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_samesite_lax_cookie()
val is_lax = (c.same_site == SameSite.Lax)
expect(is_lax).to_equal(true)
```

</details>

#### AC-6: parses SameSite=None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_samesite_none_cookie()
val is_none = (c.same_site == SameSite.None)
expect(is_none).to_equal(true)
```

</details>

#### AC-6: cookie without SameSite defaults to Lax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = parse_simple_cookie()
val is_lax = (c.same_site == SameSite.Lax)
expect(is_lax).to_equal(true)
```

</details>

### Cookie domain matching

#### AC-6: exact domain match succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_domain("example.com")
val matches = cookie_matches_domain(c, "example.com")
expect(matches).to_equal(true)
```

</details>

#### AC-6: subdomain matches dot-prefixed domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_domain(".example.com")
val matches = cookie_matches_domain(c, "sub.example.com")
expect(matches).to_equal(true)
```

</details>

#### AC-6: parent domain does not match subdomain-scoped cookie

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_domain("sub.example.com")
val matches = cookie_matches_domain(c, "example.com")
expect(matches).to_equal(false)
```

</details>

#### AC-6: unrelated domain does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_domain("example.com")
val matches = cookie_matches_domain(c, "other.com")
expect(matches).to_equal(false)
```

</details>

### Cookie path matching

#### AC-6: exact path match succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_path("/api")
val matches = cookie_matches_path(c, "/api")
expect(matches).to_equal(true)
```

</details>

#### AC-6: longer path with slash prefix matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_path("/api")
val matches = cookie_matches_path(c, "/api/resource")
expect(matches).to_equal(true)
```

</details>

#### AC-6: root path matches everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_path("/")
val matches = cookie_matches_path(c, "/any/path/here")
expect(matches).to_equal(true)
```

</details>

#### AC-6: path prefix without slash boundary does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = make_cookie_for_path("/api")
val matches = cookie_matches_path(c, "/apiother")
expect(matches).to_equal(false)
```

</details>

### CookieStore storage

#### AC-6: stored cookie is returned for matching request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = make_store_with_cookie("session", "tok1", "example.com", "/")
val cookies = get_cookies_for(store, "example.com", "/page")
expect(cookies).to_contain("session=tok1")
```

</details>

#### AC-6: cookie is not returned for non-matching domain

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = make_store_with_cookie("session", "tok1", "example.com", "/")
val cookies = get_cookies_for(store, "other.com", "/page")
val has_cookie = cookies_contain(cookies, "session")
expect(has_cookie).to_equal(false)
```

</details>

#### AC-6: cookie is not returned for non-matching path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = make_store_with_cookie("api_key", "k1", "example.com", "/api")
val cookies = get_cookies_for(store, "example.com", "/other")
val has_cookie = cookies_contain(cookies, "api_key")
expect(has_cookie).to_equal(false)
```

</details>

#### AC-6: newer cookie with same name replaces older one

1. store cookie
2. store cookie


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = make_empty_store()
store_cookie(store, make_named_cookie("token", "v1", "example.com", "/"))
store_cookie(store, make_named_cookie("token", "v2", "example.com", "/"))
val cookies = get_cookies_for(store, "example.com", "/")
expect(cookies).to_contain("token=v2")
```

</details>

#### AC-6: per-domain cap is enforced (max 50)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = make_empty_store()
val count = fill_domain_to_cap(store, "example.com", 51)
val stored = count_cookies_for_domain(store, "example.com")
expect(stored).to_be_less_than(52)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
