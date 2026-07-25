---
id: browser_net_real_site_gaps_2026-07-11
status: OPEN
severity: medium
discovered: 2026-07-11
discovered_by: Manual hardening pass against real sites (example.com, en.wikipedia.org,
  news.ycombinator.com, developer.mozilla.org, google.com plain-HTTP redirect,
  10.255.255.1, definitely-not-a-real-domain-xyz123.com) via tools/pixel_compare/fetch_url_probe.spl
related: src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl
related: src/lib/gc_async_mut/gpu/browser_engine/net/tls.spl
related: src/lib/gc_async_mut/gpu/browser_engine/net/fetch.spl
related: src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs
---

# Browser net stack: real-site gaps that need Rust-seed changes (not fixed here)

This session hardened `src/lib/gc_async_mut/gpu/browser_engine/net/**` against
real sites and fixed several real defects in pure Simple (see the "Fixed this
session" note at the bottom). The three items below need a Rust seed change
(`src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs` and/or
`rt_tls_client_*`) which is out of scope for this pass — documented per the
"do NOT fix, file a bug" instruction.

## 1. Pure-Simple TLS transport is a stub (`rt_tls_client_* == -1`)

`TlsManager.handshake()` (net/tls.spl) always fails because
`rt_tls_client_connect_with_sni` etc. are unimplemented in the interpreter
(confirmed via log: `TLS handshake failed ... runtime TLS transport
unavailable or certificate verification failed`). `H1Client.request()`
degrades explicitly and loudly to `execute_host_https` (net/h1_client.spl),
which calls the Rust-native `rt_http_request` (ureq-backed). This keeps HTTPS
fetches working end-to-end today, but the pure-Simple H1/TLS code path
(`execute_tls_http`, chunked/Content-Length body framing over
`TlsConnection.read_text`) is never exercised against a live server. No
action taken here — this needs a real `rt_tls_client_*` implementation in the
Rust seed.

## 2. `rt_http_request` does not expose response headers

`execute_host_https` (net/h1_client.spl) can only report a provenance header
(`X-Simple-Transport: host-https-fallback`) because
`rt_http_request(method, url, headers, body) -> (i64, text, text)` in
`interpreter_extern/network/mod.rs` returns `(status, body, error)` — the
`ureq::Response` headers are read (`response.status()`,
`response.into_string()`) and then dropped without ever being surfaced to
the tuple. This means every fetch that falls back to the host-HTTPS
transport (i.e. every real HTTPS fetch today, since TLS is stubbed per #1)
loses `Content-Type`, `Set-Cookie`, `Cache-Control`, `ETag`, etc. — cookie
storage and cache freshness policy silently see nothing for HTTPS responses.
Confirmed the Rust extern discards headers (read-only review, not edited):

```rust
// src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs:139-146
Ok(response) => {
    let status = response.status() as i64;
    let body = response.into_string().unwrap_or_default();
    Ok(Value::Tuple(vec![
        Value::Int(status),
        Value::Str(body),
        Value::Str(String::new()),
    ]))
}
```

Not faking headers here per instructions. Fix requires widening the
`rt_http_request` return shape (e.g. a 4th tuple element with serialized
`Name: value\r\n` header text) in the Rust seed, then updating
`execute_host_https` to parse it the same way `parse_headers` does for the
plain-HTTP path.

## 3. No connect/request timeout on `rt_http_request` — non-routable hosts take ~30s, not ~15s

`fetch https://10.255.255.1/` (non-routable) returns `Err` — it does not
hang forever — but took **~30.6s wall time** in this session, not the ~15s
target. `rt_http_request` builds `ureq::request(&method, &url)` with no
`.timeout_connect()`/`.timeout()` call, so it falls back to ureq's own
default connect timeout (~30s for an address that never responds/refuses).
There is no timeout parameter on the extern signature for pure-Simple code
to shorten this. NXDOMAIN (`definitely-not-a-real-domain-xyz123.com`) is
fine — DNS resolution fails fast (~1s) before any socket connect is
attempted, so it never reaches `rt_http_request`. Fix requires adding an
explicit timeout to the `ureq::Agent`/request builder in the Rust seed
(and ideally exposing it as an optional extern parameter so callers can
tune it per-request).

---

## Fixed this session (pure Simple, not part of this bug doc's scope)

For completeness — these were real defects found and fixed in
`net/h1_client.spl`, `net/fetch.spl`, `net/cache.spl`, `net/h2_frame.spl`,
`net/ws_crypto.spl` (all within `net/**`, no Rust changes):

- **Char/byte indexing mismatch in HTTP/1.1 response framing**
  (`net/h1_client.spl`): `parse_http_response` split the header/body
  boundary and read Content-Length/chunked bodies by indexing the decoded
  `text` response char-by-char, but Content-Length and chunk sizes are BYTE
  counts (RFC 7230). Any real response body with multi-byte UTF-8 content
  (curly quotes, non-Latin text — trivially present on
  wikipedia.org/google.com) desynced char count vs byte count and crashed
  with `string index out of bounds`. Rewritten to operate on `[u8]` for the
  header/body split and body extraction (`split_header_body_bytes`,
  `read_response_body_bytes`, `parse_chunked_body_bytes`,
  `parse_http_response_bytes`); only the (ASCII) header block is decoded to
  `text` for line-based header parsing.
- **Interpreter drops a bare trailing negative-integer literal after a run
  of single-line `if cond: return X` statements.** `hex_char_to_digit`/
  `char_to_digit` (net/h1_client.spl), `char_to_digit_val` (net/h2_frame.spl),
  `ws_hex_digit` (net/ws_crypto.spl) all ended with a bare `-1` as the
  "no match" fallback; the interpreter silently returned `nil` instead
  (confirmed with an isolated repro: `fn f(x) -> i64: if x==1: return 10 \n -1`
  returns `nil` for non-matching `x`, but `return -1` or a bare non-negative
  literal or bare string in the same position works correctly). This
  directly corrupted chunked-transfer decoding: `parse_hex("d2c")` returned
  `32` instead of `3372` because `hex_char_to_digit('d')`/`'c'` returned
  `nil`≈0 instead of 13/12, truncating every chunked real-site body to just
  its first chunk. Workaround applied: use explicit `return -1` at each of
  those call sites. The interpreter bug itself is not filed as a separate
  language-level ticket in this pass — flagging here since it's a general
  gotcha that likely affects other `if`-chain-lookup-table style functions
  across the codebase.
- **`create_redirect_request`/`attach_cookies` (net/fetch.spl) manipulated
  `FetchRequest.method`/`.headers` as if they were `HttpMethod` enum /
  `[Pair<text,text>]`, but `entity/request_types.spl` declares both as raw
  `text`.** This crashed (`unknown property or method 'first' on String`)
  the moment a plain-HTTP redirect chain actually ran (e.g.
  `http://google.com` → 301 → `http://www.google.com` → 301 →
  `https://www.google.com`). Rewritten to build/scan the raw
  `"Name: value\r\n"` header text directly, and to compare `method` as text
  (`"POST"`/`"GET"`) rather than `HttpMethod` enum patterns.
- **`attach_cookies` called `self.cookie_store.get_cookies_for(request.url)`,
  a method that does not exist on `CookieStore`** (only
  `get_header(host, path) -> text` does). This would have thrown as soon as
  any fetch used a non-`Omit` credentials mode. Fixed to call
  `get_header()` directly, which already returns the correctly formatted
  `"name=value; name2=value2"` Cookie header text.
- **`simple_parse_i64` (net/cache.spl) used `ch.char_at(0) - "0".char_at(0)`
  to compute a digit value; `char_at`/`.slice()` return `text`, not a
  codepoint int**, so subtracting two single-char `text` values threw
  `cannot convert string to int` on the first `Cache-Control: max-age=N`
  header seen (i.e. on essentially every real response). Fixed to use
  `.code_point()`.

Verified fetch matrix after fixes: `https://example.com/` (200, 559B,
"Example Domain"), `https://en.wikipedia.org/wiki/Main_Page` (200, 248519B,
"Wikipedia"), `https://news.ycombinator.com/` (200, 34754B, "Hacker News"),
`https://developer.mozilla.org/en-US/` (200, 121300B, "MDN"),
`http://google.com` → 301 → `http://www.google.com` → 301 →
`https://www.google.com` (200, 86204B, "<title>Google</title>", well-formed
`</html>` tail). Cache round-trip (`example.com` fetched twice through one
`FetchEngine`) logs `Cache hit` on the second call and returns identical
byte length, with `credentials: "include"` exercising the (now working)
cookie-attach path without crashing.
