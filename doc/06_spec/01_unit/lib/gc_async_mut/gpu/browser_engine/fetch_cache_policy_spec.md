# Fetch Cache Policy Specification

> Tests covering Browser fetch cache isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fetch Cache Policy Specification

## Scenarios

### Browser fetch cache isolation

#### only shares credential-free GET and HEAD responses

- Evaluate cache eligibility across methods and credentials
   - Expected: request_cache_eligible(cache_request("GET", "", "omit")) is true
   - Expected: request_cache_eligible(cache_request("HEAD", "", "omit")) is true
   - Expected: request_cache_eligible(cache_request("POST", "", "omit")) is false
   - Expected: request_cache_eligible(cache_request("GET", "", "include")) is false
   - Expected: request_cache_eligible(cache_request("GET", "Authorization: Bearer secret", "omit")) is false
   - Expected: request_cache_eligible(cache_request("GET", "Cookie: sid=secret", "omit")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate cache eligibility across methods and credentials")
expect(request_cache_eligible(cache_request("GET", "", "omit"))).to_equal(true)
expect(request_cache_eligible(cache_request("HEAD", "", "omit"))).to_equal(true)
expect(request_cache_eligible(cache_request("POST", "", "omit"))).to_equal(false)
expect(request_cache_eligible(cache_request("GET", "", "include"))).to_equal(false)
expect(request_cache_eligible(cache_request("GET", "Authorization: Bearer secret", "omit"))).to_equal(false)
expect(request_cache_eligible(cache_request("GET", "Cookie: sid=secret", "omit"))).to_equal(false)
```

</details>

#### does not attach same-origin credentials to cross-origin requests

- Evaluate credential attachment for same-origin and cross-origin requests
   - Expected: credentials_allow_request_cookies("omit", true) is false
   - Expected: credentials_allow_request_cookies("same-origin", true) is true
   - Expected: credentials_allow_request_cookies("same-origin", false) is false
   - Expected: credentials_allow_request_cookies("include", false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evaluate credential attachment for same-origin and cross-origin requests")
expect(credentials_allow_request_cookies("omit", true)).to_equal(false)
expect(credentials_allow_request_cookies("same-origin", true)).to_equal(true)
expect(credentials_allow_request_cookies("same-origin", false)).to_equal(false)
expect(credentials_allow_request_cookies("include", false)).to_equal(true)
```

</details>

#### admits script cookies only from an exact network URL

- Store script cookies from valid and invalid network URLs
- Logger new
- origin, "/app/next", Some
- origin, "/", Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store script cookies from valid and invalid network URLs")
var fetch = FetchEngine.new_for_origin(
    Logger.new("cookie-test", BrowserLogLevel.Error),
    "https://example.test"
)
expect(fetch.store_script_cookies(
    ["theme=dark; Path=/app"], "https://example.test/app/page"
)).to_equal(true)
expect(fetch.store_script_cookies(
    ["secret=x; HttpOnly"], "https://example.test/app/page"
)).to_equal(false)
expect(fetch.store_script_cookies(
    ["prefix=yes; Path=/", "secret=x; HttpOnly"],
    "https://example.test/app/page"
)).to_equal(false)
expect(fetch.store_script_cookies(
    ["bad=x"], "https://example.test"
)).to_equal(false)
val origin = Origin(
    scheme: "https", host: "example.test", port: 443
)
expect(fetch.cookie_store.get_header_for_origin(
    origin, "/app/next", Some(origin), "GET", false, 0
)).to_equal("theme=dark")
expect(fetch.cookie_store.get_header_for_origin(
    origin, "/", Some(origin), "GET", false, 0
).contains("prefix=yes")).to_equal(false)
```

</details>

#### bounds script cookies by serialized pair and keeps attributes outside the limit

- Store script cookies at and beyond the serialized size limit
- Logger new
- "edge=" + "x" repeat
- "edge=" + "y" repeat
   - Expected: retained.len() equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store script cookies at and beyond the serialized size limit")
var fetch = FetchEngine.new_for_origin(
    Logger.new("script-cookie-size-test", BrowserLogLevel.Error),
    "https://example.test"
)
val accepted = (
    "edge=" + "x".repeat(4091) +
    "; Secure; SameSite=None; Path=/account"
)
val rejected = (
    "edge=" + "y".repeat(4092) +
    "; Secure; SameSite=None; Path=/account"
)
expect(accepted.len()).to_be_greater_than(4096)

expect(fetch.store_script_cookies(
    [accepted], "https://example.test/account/page"
)).to_be(true)
expect(fetch.store_script_cookies(
    [rejected], "https://example.test/account/page"
)).to_be(false)
expect(fetch.store_script_cookies(
    ["bad=x\0; Path=/"], "https://example.test/"
)).to_be(false)
expect(fetch.store_script_cookies(
    ["bad=x\rbroken"], "https://example.test/"
)).to_be(false)
expect(fetch.store_script_cookies(
    ["bad=x\nbroken"], "https://example.test/"
)).to_be(false)

val origin = Origin(
    scheme: "https", host: "example.test", port: 443
)
val retained = fetch.cookie_store.script_cookie_header(
    origin, "/account/next", 0
)
expect(retained.len()).to_equal(4096)
expect(retained).to_start_with("edge=xxxx")
expect(retained.contains("edge=yyyy")).to_be(false)
expect(fetch.cookie_store.script_cookie_header(
    origin, "/", 0
)).to_equal("")
```

</details>

#### bounds raw Set-Cookie by serialized pair without charging attributes

- Process response cookies at and beyond the serialized size limit
- Logger new
- url: Url parse or opaque
- "edge=" + "x" repeat
- "edge=" + "y" repeat
- origin, "/account/next", Some
   - Expected: retained.len() equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Process response cookies at and beyond the serialized size limit")
var fetch = FetchEngine.new_for_origin(
    Logger.new("response-cookie-size-test", BrowserLogLevel.Error),
    "https://example.test"
)
val request = FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque("https://example.test/account/page"),
    headers: "",
    body: [],
    mode: RequestMode.Navigate,
    credentials: "include"
)
val accepted = (
    "edge=" + "x".repeat(4091) +
    "; Secure; SameSite=None; HttpOnly; Path=/account"
)
val rejected = (
    "edge=" + "y".repeat(4092) +
    "; Secure; SameSite=None; HttpOnly; Path=/account"
)
expect(accepted.len()).to_be_greater_than(4096)

expect(fetch.finalize_single_hop(
    request,
    FetchResponse(
        status: 200, headers: "Set-Cookie: {accepted}", body: []
    )
).is_ok()).to_be(true)
expect(fetch.finalize_single_hop(
    request,
    FetchResponse(
        status: 200, headers: "Set-Cookie: {rejected}", body: []
    )
).is_ok()).to_be(true)
expect(fetch.finalize_single_hop(
    request,
    FetchResponse(
        status: 200,
        headers: "Set-Cookie: nul=bad\0; Path=/account",
        body: []
    )
).is_ok()).to_be(true)
expect(fetch.finalize_single_hop(
    request,
    FetchResponse(
        status: 200,
        headers: "Set-Cookie: lf=bad\nvalue; Path=/account",
        body: []
    )
).is_ok()).to_be(true)
expect(fetch.finalize_single_hop(
    request,
    FetchResponse(
        status: 200,
        headers: "Set-Cookie: cr=bad\rvalue; Path=/account",
        body: []
    )
).is_ok()).to_be(true)

val origin = Origin(
    scheme: "https", host: "example.test", port: 443
)
val retained = fetch.cookie_store.get_header_for_origin(
    origin, "/account/next", Some(origin), "GET", false, 0
)
expect(retained.len()).to_equal(4096)
expect(retained).to_start_with("edge=xxxx")
expect(retained.contains("edge=yyyy")).to_be(false)
expect(retained.contains("nul=bad")).to_be(false)
expect(retained.contains("lf=bad")).to_be(false)
expect(retained.contains("cr=bad")).to_be(false)
expect(fetch.cookie_store.script_cookie_header(
    origin, "/account/next", 0
)).to_equal("")
```

</details>

#### rejects a whole script batch that would shadow a Secure cookie

- Attempt an insecure script batch that shadows a Secure cookie
- Logger new
- parse set cookie
- insecure origin, "/", Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt an insecure script batch that shadows a Secure cookie")
var fetch = FetchEngine.new_for_origin(
    Logger.new("cookie-atomic-test", BrowserLogLevel.Error),
    "http://example.test"
)
val secure_origin = Origin(
    scheme: "https", host: "example.test", port: 443
)
val _ = fetch.cookie_store.store_from_origin(
    parse_set_cookie("session=live; Path=/; Secure"),
    secure_origin,
    100
)
expect(fetch.store_script_cookies(
    ["prefix=yes; Path=/", "session=shadow; Path=/"],
    "http://example.test/"
)).to_equal(false)
val insecure_origin = Origin(
    scheme: "http", host: "example.test", port: 80
)
expect(fetch.cookie_store.get_header_for_origin(
    insecure_origin, "/", Some(insecure_origin), "GET", false, 100
).contains("prefix=yes")).to_equal(false)
```

</details>

#### preserves Lax cookies for cross-site top-level navigation only

- Prepare cross-site subresource and top-level navigation requests
- Logger new
- url: Url parse or opaque
- Err
- Ok
- Err
- Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare cross-site subresource and top-level navigation requests")
var fetch = FetchEngine.new_for_origin(
    Logger.new("same-site-test", BrowserLogLevel.Error),
    "https://other.test"
)
expect(fetch.store_script_cookies(
    ["lax=yes; SameSite=Lax; Path=/"],
    "https://example.test/start"
)).to_equal(true)
val request = FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque("https://example.test/next"),
    headers: "",
    body: [],
    mode: RequestMode.Navigate,
    credentials: "include"
)
match fetch.prepare_single_hop(
    request, "https://other.test/", false
):
    Err(error): fail(error.message)
    Ok(prepared):
        expect(prepared.request.headers.contains("Cookie:")).to_equal(
            false
        )
match fetch.prepare_single_hop(
    request, "https://other.test/", true
):
    Err(error): fail(error.message)
    Ok(prepared):
        expect(prepared.request.headers).to_contain("Cookie: lax=yes")
```

</details>

#### treats max-age zero as immediately stale

- Store and look up a response with max-age zero
- Logger new


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Store and look up a response with max-age zero")
var cache = HttpCache.new(
    Logger.new("cache-test", BrowserLogLevel.Error), 1
)
expect(cache.store(
    "https://example.test/site.css", [1u8, 2u8],
    "Cache-Control: max-age=0"
).is_ok()).to_equal(true)
expect(cache.lookup(
    "https://example.test/site.css"
)).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_cache_policy_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser fetch cache isolation.
- Browser fetch cache isolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
