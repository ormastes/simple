# Cookie Store Specification

> Verifies RFC 6265 cookie domain/path matching, SameSite enum, Set-Cookie parsing, and CookieStore storage/retrieval. No network calls — pure logic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

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
| Source | `test/unit/browser_engine/net/cookie_store_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies RFC 6265 cookie domain/path matching, SameSite enum, Set-Cookie parsing,
and CookieStore storage/retrieval. No network calls — pure logic.

## Scenarios

### parse_set_cookie

#### AC-6: parses simple name=value

- Parse a simple name-value cookie
   - Expected: c.name equals `session`
   - Expected: c.value equals `abc123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a simple name-value cookie")
val c = parse_simple_cookie()
expect(c.name).to_equal("session")
expect(c.value).to_equal("abc123")
```

</details>

#### AC-6: parses Domain attribute

- Parse a cookie with a Domain attribute
   - Expected: c.domain equals `example.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a cookie with a Domain attribute")
val c = parse_cookie_with_domain()
expect(c.domain).to_equal("example.com")
```

</details>

#### AC-6: parses Path attribute

- Parse a cookie with a Path attribute
   - Expected: c.path equals `/api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a cookie with a Path attribute")
val c = parse_cookie_with_path()
expect(c.path).to_equal("/api")
```

</details>

#### AC-6: parses Secure flag

- Parse a cookie with the Secure flag
   - Expected: c.secure is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a cookie with the Secure flag")
val c = parse_secure_cookie()
expect(c.secure).to_equal(true)
```

</details>

#### AC-6: parses HttpOnly flag

- Parse a cookie with the HttpOnly flag
   - Expected: c.http_only is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a cookie with the HttpOnly flag")
val c = parse_httponly_cookie()
expect(c.http_only).to_equal(true)
```

</details>

#### AC-6: parses SameSite=Strict

- Parse a SameSite Strict cookie
   - Expected: is_strict is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a SameSite Strict cookie")
val c = parse_samesite_strict_cookie()
val is_strict = (c.same_site == SameSite.Strict)
expect(is_strict).to_equal(true)
```

</details>

#### AC-6: parses SameSite=Lax

- Parse a SameSite Lax cookie
   - Expected: is_lax is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a SameSite Lax cookie")
val c = parse_samesite_lax_cookie()
val is_lax = (c.same_site == SameSite.Lax)
expect(is_lax).to_equal(true)
```

</details>

#### AC-6: parses SameSite=None

- Parse a SameSite None cookie
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a SameSite None cookie")
val c = parse_samesite_none_cookie()
val is_none = (c.same_site == SameSite.None)
expect(is_none).to_equal(true)
```

</details>

#### AC-6: cookie without SameSite defaults to Lax

- Parse a cookie without a SameSite attribute
   - Expected: is_lax is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse a cookie without a SameSite attribute")
val c = parse_simple_cookie()
val is_lax = (c.same_site == SameSite.Lax)
expect(is_lax).to_equal(true)
```

</details>

#### AC-6: attribute names and values are case-insensitive

- Parse mixed-case cookie attributes
   - Expected: c.domain equals `example.com`
   - Expected: c.secure is true
   - Expected: c.same_site == SameSite.Strict is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse mixed-case cookie attributes")
val c = parse_set_cookie("token=x; dOmAiN=example.com; sAmEsItE=sTrIcT; SeCuRe")
expect(c.domain).to_equal("example.com")
expect(c.secure).to_equal(true)
expect(c.same_site == SameSite.Strict).to_equal(true)
```

</details>

#### AC-6: derives default path and preserves an explicit absolute Path

- Apply default and explicit cookie paths
   - Expected: absent.path equals `/account`
   - Expected: explicit.path equals `/chosen`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply default and explicit cookie paths")
val absent = apply_default_path(parse_set_cookie("a=1"), "a=1", "/account/login")
val explicit = apply_default_path(parse_set_cookie("a=1; Path=/chosen"), "a=1; Path=/chosen", "/account/login")
expect(absent.path).to_equal("/account")
expect(explicit.path).to_equal("/chosen")
```

</details>

#### AC-6: parses RFC1123 Expires and gives valid Max-Age precedence

- Apply valid and malformed cookie expiration attributes
   - Expected: expires.expires_at equals `1445412480`
   - Expected: malformed.expires_at equals `0`
   - Expected: override.expires_at equals `110`
   - Expected: epoch.expires_at equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply valid and malformed cookie expiration attributes")
val expires = apply_max_age(parse_set_cookie("a=1"), "a=1; Expires=Wed, 21 Oct 2015 07:28:00 GMT", 100)
val malformed = apply_max_age(parse_set_cookie("a=1"), "a=1; Expires=not-a-date", 100)
val override = apply_max_age(parse_set_cookie("a=1"), "a=1; Expires=Wed, 21 Oct 2015 07:28:00 GMT; Max-Age=10", 100)
val epoch = apply_max_age(parse_set_cookie("a=1"), "a=1; Expires=Thu, 01 Jan 1970 00:00:00 GMT", 100)
expect(expires.expires_at).to_equal(1445412480)
expect(malformed.expires_at).to_equal(0)
expect(override.expires_at).to_equal(110)
expect(epoch.expires_at).to_equal(-1)
```

</details>

### Cookie domain matching

#### AC-6: exact domain match succeeds

- Match a cookie against its exact domain
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a cookie against its exact domain")
val c = make_cookie_for_domain("example.com")
val matches = cookie_matches_domain(c, "example.com")
expect(matches).to_equal(true)
```

</details>

#### AC-6: subdomain matches dot-prefixed domain

- Match a subdomain against a dot-prefixed cookie domain
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a subdomain against a dot-prefixed cookie domain")
val c = make_cookie_for_domain(".example.com")
val matches = cookie_matches_domain(c, "sub.example.com")
expect(matches).to_equal(true)
```

</details>

#### AC-6: parent domain does not match subdomain-scoped cookie

- Match a parent domain against a subdomain-scoped cookie
   - Expected: matches is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a parent domain against a subdomain-scoped cookie")
val c = make_cookie_for_domain("sub.example.com")
val matches = cookie_matches_domain(c, "example.com")
expect(matches).to_equal(false)
```

</details>

#### AC-6: unrelated domain does not match

- Match an unrelated domain against the cookie domain
   - Expected: matches is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match an unrelated domain against the cookie domain")
val c = make_cookie_for_domain("example.com")
val matches = cookie_matches_domain(c, "other.com")
expect(matches).to_equal(false)
```

</details>

### Cookie path matching

#### AC-6: exact path match succeeds

- Match a cookie against its exact path
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a cookie against its exact path")
val c = make_cookie_for_path("/api")
val matches = cookie_matches_path(c, "/api")
expect(matches).to_equal(true)
```

</details>

#### AC-6: longer path with slash prefix matches

- Match a descendant request path at a slash boundary
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a descendant request path at a slash boundary")
val c = make_cookie_for_path("/api")
val matches = cookie_matches_path(c, "/api/resource")
expect(matches).to_equal(true)
```

</details>

#### AC-6: root path matches everything

- Match the root cookie path against a nested request path
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match the root cookie path against a nested request path")
val c = make_cookie_for_path("/")
val matches = cookie_matches_path(c, "/any/path/here")
expect(matches).to_equal(true)
```

</details>

#### AC-6: path prefix without slash boundary does not match

- Match a request path without the required slash boundary
   - Expected: matches is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match a request path without the required slash boundary")
val c = make_cookie_for_path("/api")
val matches = cookie_matches_path(c, "/apiother")
expect(matches).to_equal(false)
```

</details>

### CookieStore storage

#### AC-6: stored cookie is returned for matching request

- Store a cookie and request its matching path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store a cookie and request its matching path")
val store = make_store_with_cookie("session", "tok1", "example.com", "/")
val cookies = get_cookies_for(store, "example.com", "/page")
expect(cookies).to_contain("session=tok1")
```

</details>

#### AC-6: cookie is not returned for non-matching domain

- Request a stored cookie from a different domain
   - Expected: has_cookie is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request a stored cookie from a different domain")
val store = make_store_with_cookie("session", "tok1", "example.com", "/")
val cookies = get_cookies_for(store, "other.com", "/page")
val has_cookie = cookies_contain(cookies, "session")
expect(has_cookie).to_equal(false)
```

</details>

#### AC-6: cookie is not returned for non-matching path

- Request a stored cookie from a different path
   - Expected: has_cookie is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request a stored cookie from a different path")
val store = make_store_with_cookie("api_key", "k1", "example.com", "/api")
val cookies = get_cookies_for(store, "example.com", "/other")
val has_cookie = cookies_contain(cookies, "api_key")
expect(has_cookie).to_equal(false)
```

</details>

#### AC-6: newer cookie with same name replaces older one

- Store two values under the same cookie identity
- store cookie
- store cookie


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store two values under the same cookie identity")
val store = make_empty_store()
store_cookie(store, make_named_cookie("token", "v1", "example.com", "/"))
store_cookie(store, make_named_cookie("token", "v2", "example.com", "/"))
val cookies = get_cookies_for(store, "example.com", "/")
expect(cookies).to_contain("token=v2")
```

</details>

#### AC-6: per-domain cap is enforced (max 50)

- Fill one cookie domain beyond its storage cap


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill one cookie domain beyond its storage cap")
val store = make_empty_store()
val count = fill_domain_to_cap(store, "example.com", 51)
val stored = count_cookies_for_domain(store, "example.com")
expect(stored).to_be_less_than(52)
```

</details>

#### AC-6: total cookie count is bounded

- Fill the cookie store beyond its total cap
- store store
   - Expected: store.count() equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill the cookie store beyond its total cap")
val store = make_empty_store()
var i = 0
while i < 3001:
    store.store(make_named_cookie("cookie", "v", "d{i}.example", "/"))
    i = i + 1
expect(store.count()).to_equal(3000)
```

</details>

#### AC-6: Max-Age zero removes the matching cookie

- Replace a live cookie with Max-Age zero
- store store from origin
- store store from origin
   - Expected: store.get_header_for_origin(origin, "/", Some(origin), "GET", false, 101) equals ``
   - Expected: store.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace a live cookie with Max-Age zero")
val store = make_empty_store()
val origin = Origin(scheme: "https", host: "example.com", port: 443)
val live = parse_set_cookie("session=live; Path=/")
store.store_from_origin(live, origin, 100)
val expired = apply_max_age(parse_set_cookie("session=gone; Path=/; Max-Age=0"), "session=gone; Path=/; Max-Age=0", 101)
store.store_from_origin(expired, origin, 101)
expect(store.get_header_for_origin(origin, "/", Some(origin), "GET", false, 101)).to_equal("")
expect(store.count()).to_equal(0)
```

</details>

#### AC-6: script cannot set or replace HttpOnly cookies

- Attempt to set and replace HttpOnly cookies from script
- store store from origin
   - Expected: set_result.accepted is false
   - Expected: replace_result.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt to set and replace HttpOnly cookies from script")
val store = make_empty_store()
val origin = Origin(scheme: "https", host: "example.com", port: 443)
store.store_from_origin(parse_set_cookie("session=secret; Path=/; HttpOnly"), origin, 100)
val set_result = store.store_from_script(parse_set_cookie("other=x; Path=/; HttpOnly"), origin, 101)
val replace_result = store.store_from_script(parse_set_cookie("session=visible; Path=/"), origin, 101)
expect(set_result.accepted).to_equal(false)
expect(replace_result.accepted).to_equal(false)
expect(store.get_header_for_origin(origin, "/", Some(origin), "GET", false, 101)).to_contain("session=secret")
```

</details>

#### AC-6: insecure origin cannot shadow a Secure cookie

- Attempt to shadow a Secure cookie from an insecure origin
- store store from origin
   - Expected: verdict.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt to shadow a Secure cookie from an insecure origin")
val store = make_empty_store()
val secure_origin = Origin(scheme: "https", host: "example.com", port: 443)
val insecure_origin = Origin(scheme: "http", host: "sub.example.com", port: 80)
store.store_from_origin(parse_set_cookie("session=live; Domain=example.com; Path=/login/; Secure"), secure_origin, 100)
val shadow = parse_set_cookie("session=shadow; Domain=sub.example.com; Path=/login/admin")
val verdict = store.store_from_origin(shadow, insecure_origin, 101)
expect(verdict.accepted).to_equal(false)
val target = Origin(scheme: "https", host: "sub.example.com", port: 443)
expect(store.get_header_for_origin(target, "/login/admin", Some(target), "GET", false, 101)).to_contain("session=live")
```

</details>

#### AC-6: applies the 4096-byte limit to UTF-8 name=value

- Store UTF-8 cookies at and beyond the serialized size limit
   - Expected: store.count() equals `1`
- origin, "/", Some
   - Expected: header equals `"edge=" + accepted_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store UTF-8 cookies at and beyond the serialized size limit")
val store = make_empty_store()
val origin = Origin(scheme: "https", host: "example.com", port: 443)
val accepted_value = "😀".repeat(1022) + "xxx"
val rejected_value = "😀".repeat(1023)
val accepted = parse_set_cookie(
    "edge=" + accepted_value +
    "; Secure; SameSite=None; Partitioned; Path=/"
)
val rejected = parse_set_cookie(
    "edge=" + rejected_value +
    "; Secure; SameSite=None; Partitioned; Path=/"
)
val partition_key = "https://example.com"

val accepted_verdict = store.store_from_origin(
    accepted, origin, 100, partition_key
)
val rejected_verdict = store.store_from_origin(
    rejected, origin, 101, partition_key
)

expect(accepted_verdict.accepted).to_be(true)
expect(rejected_verdict.accepted).to_be(false)
expect(rejected_verdict.reason).to_equal(
    "cookie-exceeds-4096-byte-limit"
)
expect(store.count()).to_equal(1)
val header = store.get_header_for_origin(
    origin, "/", Some(origin), "GET", false, 101, partition_key
)
expect(header).to_equal("edge=" + accepted_value)
expect(header.contains(rejected_value)).to_be(false)
```

</details>

#### AC-6: orders request and script cookies by path then creation

- Store cookies across paths, partitions, and creation times
- parse set cookie
- parse set cookie
- parse set cookie
- parse set cookie
- origin, "/app/admin/settings/page", Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store cookies across paths, partitions, and creation times")
val store = make_empty_store()
val origin = Origin(scheme: "https", host: "example.com", port: 443)
val top_partition = "https://top.example"
val other_partition = "https://other.example"
val _ = store.store_from_origin(
    parse_set_cookie("root=base; Path=/"), origin, 100
)
val _ = store.store_from_origin(
    parse_set_cookie("same_first=one; Path=/app"), origin, 101
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "private=secret; HttpOnly; Path=/app/admin"
    ),
    origin, 102
)
val _ = store.store_from_origin(
    parse_set_cookie("same_second=two; Path=/app"), origin, 103
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "partition=top; Secure; SameSite=None; Partitioned; " +
        "Path=/app/admin/settings"
    ),
    origin, 104, top_partition
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "partition=other; Secure; SameSite=None; Partitioned; " +
        "Path=/app/admin/settings"
    ),
    origin, 105, other_partition
)
val _ = store.store_from_origin(
    parse_set_cookie("same_first=updated; Path=/app"), origin, 106
)

val network = store.get_header_for_origin(
    origin, "/app/admin/settings/page", Some(origin),
    "GET", false, 107, top_partition
)
val script = store.script_cookie_header(
    origin, "/app/admin/settings/page", 107, top_partition
)
expect(network).to_equal(
    "partition=top; private=secret; same_first=updated; " +
    "same_second=two; root=base"
)
expect(script).to_equal(
    "partition=top; same_first=updated; same_second=two; root=base"
)
```

</details>

#### AC-6: preserves global creation order across jars and replacement

- Store and replace same-path cookies across domain jars
- parse set cookie
- parse set cookie
- parse set cookie
- child, "/", Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store and replace same-path cookies across domain jars")
val store = make_empty_store()
val parent = Origin(
    scheme: "https", host: "example.com", port: 443
)
val child = Origin(
    scheme: "https", host: "sub.example.com", port: 443
)
val _ = store.store_from_origin(
    parse_set_cookie("parent_first=one; Domain=example.com; Path=/"),
    parent, 100
)
val _ = store.store_from_origin(
    parse_set_cookie("child_second=two; Path=/"), child, 101
)
val _ = store.store_from_origin(
    parse_set_cookie("parent_third=three; Domain=example.com; Path=/"),
    parent, 102
)
val _ = store.store_from_origin(
    parse_set_cookie(
        "parent_first=updated; Domain=example.com; Path=/"
    ),
    parent, 103
)

expect(store.get_header_for_origin(
    child, "/", Some(child), "GET", false, 104
)).to_equal(
    "parent_first=updated; child_second=two; parent_third=three"
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
