# Lane URLPARSE — fail-closed URL parsing

Status: DONE (not committed). Spec green 66/66 in both JIT and interpreter;
both deliberate-red calibrations caught; no consumer regressed.

## Verification

- Spec `test/01_unit/std/http_client/url_parse_spec.spl` — 9 describe blocks,
  **66 examples, 0 failures**, identical under
  `SIMPLE_EXECUTION_MODE=interpreter`.
- Truth-table probe `build/urlparse_probe/probe_installed.spl` — JIT vs
  interpreter output byte-identical (`installed_jit.txt` vs
  `installed_interp.txt`).

### Deliberate-red calibration 1 — re-introduce the lenient `http` default
Patched `parse_url` to return `Some(UrlParts(scheme: "http", host: trimmed,
port: 80, path: "/"))` on every path that now returns `None` for a bad scheme.
Result: **9 failures** (`build/urlparse_probe/spec_red_cal1.txt`)

    ✗ rejects plainly malformed input
    ✗ no longer makes two malformed inputs mutually same-origin
    ✗ rejects a protocol-relative URL (no scheme to trust)
    ✗ rejects a special scheme with no authority
    ✗ rejects a scheme that does not start with a letter
    ✗ joins a relative path onto a base
    ✗ fails the join when the base is unparseable
    ✗ fails the join when the base is opaque
    ✗ fails add_query_param on an unparseable URL

### Deliberate-red calibration 2 — restore the `Option`-into-`i64` port leak
Replaced `_url_parse_port` with the original `port = ptxt.parse_int()`.
Result: **3 failures** (`build/urlparse_probe/spec_red_cal2.txt`)

    ✗ rejects a non-numeric port instead of leaking an Option
    ✗ rejects an out-of-range port
    ✗ rejects port 0

Both reverted; re-verified 66/66 green (`build/urlparse_probe/spec_green2.txt`).

## Consumer impact

| Consumer | Change | Verdict |
|---|---|---|
| `http_client/connection.spl` `serialize_request` (x3 tiers) | fails closed with `""` instead of a request aimed at a guessed host | lint clean; COLL006 count unchanged from HEAD (3) |
| `http_client/types.spl` `url_join` / `add_query_param` / `remove_query_param` | now `Option<text>`; **no external callers** | covered by the new spec |
| `browser_engine/net/entity/url_types.spl` `Url.parse` | now `Option<Url>`; `Url` gained `opaque`; `authority()`/`Origin.to_text()` use `url_default_port` (ws/wss/ftp were wrong before) | see below |
| `browser_engine/script/network_api.spl` `script_parse_url` | 4th duplicate collapsed into `Url.parse`; unparseable ⇒ opaque `Url`, never an `http` origin | — |
| `browser_engine/net/fetch.spl` `resolve_fetch_redirect_url` | now `Option<Url>`; an unparseable `Location:` aborts the redirect instead of resolving to a guessed origin | — |
| `web/browser_session_loading.spl` HSTS host lookup | returns the URL unchanged when unparseable | — |
| `os/hosted/hosted_browser_renderer_policy.spl` | `hosted_browser_canonical_http_url` → `""`, `hosted_browser_hsts_upgrade_valid` → `false`, `hosted_browser_network_origin` → `""` on failure | — |
| `os/hosted/hosted_browser_renderer_process.spl` | navigation + fetch redirect paths return `invalid-navigation-redirect` on failure | — |
| `os/hosted/hosted_web_content_session.spl` | uses `Url.parse_or_opaque` (no failure channel available) | — |

### Consumer spec verdicts

| Spec | Result |
|---|---|
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl` | 5 examples, **0 failures** |
| `.../fetch_cache_policy_spec.spl` | 2 examples, **0 failures** |
| `.../h1_client_request_spec.spl` | 2 failures — **baseline (HEAD lib + HEAD spec) has 3**. My change *fixed* "includes a non-default port in HTTP authority" (the `url_default_port` fix); the other two ("decodes bounded complete chunks", "serializes raw request headers once") are pre-existing and unrelated to URLs. |
| `test/01_unit/os/hosted/hosted_browser_renderer_policy_spec.spl` | does not compile — `parse: in browser_session.spl: Unexpected token: expected Fn, found Self_`. **Pre-existing**: reproduced with my `browser_session_loading.spl` edit reverted to HEAD; `browser_session.spl` is untouched by this lane (concurrent "me receiver" compiler work). |
| `test/01_unit/browser_engine/security/origin_model_spec.spl` (BRORIGIN) | 10 failures with my change, **10 failures at baseline** — byte-identical count, unaffected. Those are BRORIGIN's in-flight cookie public-suffix tests. |

Specs repaired (call sites only, `Url.parse(` → `Url.parse_or_opaque(`, all
inputs are valid URLs so behaviour is unchanged): `tls_policy_spec.spl` (5),
`fetch_cache_policy_spec.spl` (1), `h1_client_request_spec.spl` (5),
`hosted_browser_renderer_policy_spec.spl` (2).

## Filed

`doc/08_tracking/bug/lint_coll006_false_positive_substring_scan_loop_2026-07-27.md`
— COLL006 fires on `while` loops that contain no string concatenation at all
(`_url_parse_port`, `_url_valid_host`, `_url_valid_ipv6` have no `+` on text).
The one genuine COLL006 introduced here (`_url_strip_tabs` building with
`out = out + c`) was rewritten as `split(sep).join("")`.

## Landmine hit

A parallel session's working-copy sync **reverted every `src/**` edit** of this
lane mid-flight (HEAD moved to `e0f6d761320`). Re-application is scripted and
idempotent: `sh build/urlparse_probe/apply.sh` restores the `types.spl` and
`connection.spl` edits across all three tiers from
`build/urlparse_probe/types_tail.spl`. Re-run it if the edits vanish again.

## Parser locations (and duplicates)

| # | Path | Kind | Action |
|---|------|------|--------|
| 1 | `src/lib/nogc_sync_mut/http_client/types.spl` | `parse_url` — the broken one | **fixed (canonical)** |
| 2 | `src/lib/gc_async_mut/http_client/types.spl` | byte-identical tier copy of #1 | fixed (mirrored) |
| 3 | `src/lib/nogc_async_mut/http_client/types.spl` | byte-identical tier copy of #1 | fixed (mirrored) |
| 4 | `src/lib/gc_async_mut/gpu/browser_engine/net/entity/url_types.spl` `Url.parse` | thin wrapper over #2 | fixed, now `Option<Url>` |
| 5 | `src/lib/gc_async_mut/gpu/browser_engine/script/network_api.spl` `script_parse_url` | **4th hand-rolled copy**, also defaulted `scheme=http` | **collapsed** — now delegates to `Url.parse` |
| 6 | `src/lib/blink/url/url_parser.spl` `parse_url` | 5th independent parser (Blink tree) | NOT touched — reported for convergence |
| 7 | `src/compiler_rust/lib/std/src/tooling/url_utils.spl` `parse_url -> Option<Url>` | already Option-returning | out of scope (`src/compiler_rust/**` excluded) |
| 8 | `src/os/tools/net/wget_tool.spl` `_parse_url -> Result<ParsedUrl, text>` | already Result-returning, tool-local | left alone |
| 9 | `.../security/origin_policy.spl` (BRORIGIN) | independent origin derivation | not touched (other lane) |

## Root causes fixed

1. **Silent `http` default.** No `://` ⇒ `scheme = "http"`, and the whole input
   became the host. `""`, `"   "`, `"not a url"` all produced `("http", "")` or
   `("http", <garbage>)`, so every malformed URL was mutually same-origin.
2. **Non-special schemes destroyed.** `data:`/`about:`/`javascript:` have no
   `://`, so they hit the `http` default and their scheme text became the host
   (`host=data`, `host=about`, `host=javascript`).
3. **`Option<i64>` leaked into an `i64` field.** `port = port_str.parse_int()`
   assigned the `Option` struct into a var declared `i64`. The interpreter
   proves it directly:
   `error: semantic: method to_string not found on type enum (receiver value: Option::None)`.
   On the JIT the same assignment is silent pointer garbage (BRORIGIN observed
   640 / 3544 / 216). Fixed by `_url_parse_port` returning a plain `i64` with
   `-1` as the failure sentinel — no Option ever reaches the `port` field.
4. **Userinfo host spoof.** `http://user:pw@example.com/` parsed `host=user`;
   `http://good.com@evil.com/` would have parsed `host=good.com`. Now split on
   the **last** `@`.
5. **IPv6 literals destroyed.** `http://[::1]:8080/` parsed `host="["`.

## Truth table — before vs after

`scheme | host | port | path` (query/fragment omitted where empty).
"FAIL" = `None` (fail-closed).

| Input | BEFORE (unsafe) | AFTER (WHATWG-informed) |
|---|---|---|
| `http://example.com/` | `http\|example.com\|80\|/` | same |
| `http://example.com` | `http\|example.com\|80\|/` | same |
| `https://example.com/a/b?c=d#e` | `https\|example.com\|443\|/a/b` q=`c=d` f=`e` | same |
| `http://example.com:8080/p` | `http\|example.com\|8080\|/p` | same |
| `http://example.com:80/` | `http\|example.com\|80\|/` | same |
| `https://example.com:443/` | `https\|example.com\|443\|/` | same |
| `data:text/plain,hello` | **`http\|data\|<Option>\|/plain,hello`** | `data\|\|0\|text/plain,hello` opaque |
| `about:blank` | **`http\|about\|<Option>\|/`** | `about\|\|0\|blank` opaque |
| `javascript:alert(1)` | **`http\|javascript\|<Option>\|/`** | `javascript\|\|0\|alert(1)` opaque |
| `mailto:a@b.com` | **`http\|mailto\|<Option>\|/`** | `mailto\|\|0\|a@b.com` opaque |
| `file:///tmp/x` | `file\|\|**80**\|/tmp/x` | `file\|\|0\|/tmp/x` |
| `file://host:80/x` | `file\|host\|80\|/x` | **FAIL** (file takes no port) |
| `ws://example.com/s` | `ws\|example.com\|**80**\|/s` | `ws\|example.com\|80\|/s` |
| `wss://example.com/s` | `wss\|example.com\|**80**\|/s` | `wss\|example.com\|**443**\|/s` |
| `ftp://example.com/f` | `ftp\|example.com\|**80**\|/f` | `ftp\|example.com\|**21**\|/f` |
| `http://user:pw@example.com/p` | **`http\|user\|<Option>\|/p`** | `http\|example.com\|80\|/p` |
| `http://good.com@evil.com/` | **`http\|good.com\|80\|/`** (spoof) | `http\|evil.com\|80\|/` |
| `http://[::1]:8080/` | **`http\|[\|<Option>\|/`** | `http\|[::1]\|8080\|/` |
| `http://[::1]/` | `http\|[::1]\|80\|/` | same |
| `http://[FE80::1]/` | `http\|[FE80::1]\|80\|/` | `http\|[fe80::1]\|80\|/` |
| `http://[::1/` | `http\|[::1\|80\|/` | **FAIL** |
| `HTTP://EXAMPLE.COM/P` | **`HTTP\|EXAMPLE.COM\|80\|/P`** | `http\|example.com\|80\|/P` |
| `http://example.com./` | `http\|example.com.\|80\|/` | same (trailing dot preserved) |
| `http://exa\tmple.com/` | tab kept in host | tab stripped (split/join) |
| `  https://example.com/  ` | leading spaces in scheme | trimmed |
| `""` | **`http\|\|80\|/`** | **FAIL** |
| `"   "` | **`http\|"   "\|80\|/`** | **FAIL** |
| `not a url` | **`http\|not a url\|80\|/`** | **FAIL** |
| `http://example.com:abc/` | **`http\|example.com\|<Option>\|/`** | **FAIL** |
| `http://example.com:99999/` | `http\|example.com\|99999\|/` | **FAIL** |
| `http://example.com:0/` | `http\|example.com\|0\|/` | **FAIL** (0 collides with the no-port sentinel) |
| `http://:8080/` | `http\|\|8080\|/` | **FAIL** (empty host) |
| `http:example.com/` | `http\|\|80\|/` | **FAIL** (special scheme needs `//`) |
| `//example.com/p` | **`http\|\|80\|//example.com/p`** | **FAIL** (no scheme to trust) |
| `1http://example.com/` | `1http\|example.com\|80\|/` | **FAIL** (scheme must start with a letter) |
| `http://exa\|mple.com/` | `http\|exa\|mple.com\|80\|/` | **FAIL** (forbidden host code point) |
| `http://example.com:/x` | `http\|example.com\|<Option>\|/x` | `http\|example.com\|80\|/x` |

Raw evidence: `build/urlparse_probe/before_{jit,interp}.txt`,
`build/urlparse_probe/installed_{jit,interp}.txt` (JIT vs interpreter A/B
identical for the fixed parser).

## API changes

- `parse_url(url: text) -> Option<UrlParts>` (was a 6-tuple with an unsafe default)
- new `pub class UrlParts { scheme host port path query fragment opaque }`
- new `url_default_port(scheme) -> i64`, `url_is_special(scheme) -> bool`
- `url_join`, `add_query_param`, `remove_query_param` → `Option<text>`
- `Url.parse(raw) -> Option<Url>`; new `Url.opaque_invalid`, `Url.parse_or_opaque`, `Url.valid()`
- `Url` gained an `opaque: bool` field
- `resolve_fetch_redirect_url(base, location) -> Option<Url>`

## Follow-up (do NOT do here)

- BRORIGIN's `security/origin_policy.spl` derives origins itself precisely
  because `Url.parse` could not be trusted. The parser now satisfies every
  property that derivation was written to guarantee (opaque non-special
  schemes, fail-closed on malformed input, lowercase normalization, real i64
  port, last-`@` host). It can now delegate — **convergence follow-up, other
  lane's file.**
- `src/lib/blink/url/url_parser.spl` is a 5th independent parser and should
  collapse into this one (master plan §4).
