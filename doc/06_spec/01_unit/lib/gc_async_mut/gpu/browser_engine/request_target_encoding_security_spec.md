# request_target_encoding_security_spec

> One parsed URL must produce the same ASCII request target for HTTP/1.1,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# request_target_encoding_security_spec

One parsed URL must produce the same ASCII request target for HTTP/1.1,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


One parsed URL must produce the same ASCII request target for HTTP/1.1,
HTTP/2, and WebSocket handshakes. Raw UTF-8 and control bytes never reach a
request line or `:path`; existing escapes remain byte-exact and fragments,
authority, and user information stay outside the target.

## Scenarios

### Browser request-target encoding security

#### should serialize one safe target across HTTP and WebSocket transports

- Verify: should serialize one safe target across HTTP and WebSocket transports
- Resolve redirect references and build producer controls
   - Expected: next.path equals `/dir/next`
   - Expected: next.query equals `q=1`
   - Expected: next.fragment equals `fresh`
   - Expected: next.authority() equals `safe.test`
   - Expected: next.request_target() equals `/dir/next?q=1`
   - Expected: fragment.path equals `/dir/page`
   - Expected: fragment.query equals `old=1`
   - Expected: fragment.fragment equals `fresh`
   - Expected: fragment.request_target() equals `/dir/page?old=1`
   - Expected: root.authority() equals `safe.test`
   - Expected: root.path equals `/login`
   - Expected: root.query equals `return=https://id.test/`
   - Expected: query_only.authority() equals `safe.test`
   - Expected: query_only.path equals `/dir/page`
   - Expected: query_only.query equals `return=https://id.test/`
   - Expected: relative_url.authority() equals `safe.test`
   - Expected: relative_url.path equals `/dir/next`
   - Expected: relative_url.query equals `return=https://id.test/`
   - Expected: url.request_target() equals `expected`
- Serialize the exact target into the HTTP/1.1 request line
- Serialize the exact target into the HTTP/2 path pseudo-header
   - Expected: h2_headers[3].first equals `:path`
   - Expected: h2_headers[3].second equals `expected`
- Serialize the exact target into the WebSocket opening handshake
   - Expected: ws_request_path(url) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 104 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-011
step("Verify: should serialize one safe target across HTTP and WebSocket transports")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Resolve redirect references and build producer controls")
val base = Url.parse_or_opaque(
    "https://safe.test/dir/page?old=1#old"
)
val relative = resolve_fetch_redirect_url(base, "next?q=1#fresh")
if not relative.?:
    fail("relative redirect was not resolved")
val next = relative!
expect(next.path).to_equal("/dir/next")
expect(next.query).to_equal("q=1")
expect(next.fragment).to_equal("fresh")
expect(next.authority()).to_equal("safe.test")
expect(next.request_target()).to_equal("/dir/next?q=1")

val fragment_only = resolve_fetch_redirect_url(base, "#fresh")
if not fragment_only.?:
    fail("fragment redirect was not resolved")
val fragment = fragment_only!
expect(fragment.path).to_equal("/dir/page")
expect(fragment.query).to_equal("old=1")
expect(fragment.fragment).to_equal("fresh")
expect(fragment.request_target()).to_equal("/dir/page?old=1")

val root_data = resolve_fetch_redirect_url(
    base, "/login?return=https://id.test/"
)
if not root_data.?:
    fail("root-relative redirect was not resolved")
val root = root_data!
expect(root.authority()).to_equal("safe.test")
expect(root.path).to_equal("/login")
expect(root.query).to_equal("return=https://id.test/")
expect(root.request_target()).to_equal(
    "/login?return=https://id.test/"
)

val query_data = resolve_fetch_redirect_url(
    base, "?return=https://id.test/"
)
if not query_data.?:
    fail("query-only redirect was not resolved")
val query_only = query_data!
expect(query_only.authority()).to_equal("safe.test")
expect(query_only.path).to_equal("/dir/page")
expect(query_only.query).to_equal("return=https://id.test/")
expect(query_only.request_target()).to_equal(
    "/dir/page?return=https://id.test/"
)

val relative_data = resolve_fetch_redirect_url(
    base, "next?return=https://id.test/"
)
if not relative_data.?:
    fail("relative redirect with URL query data was not resolved")
val relative_url = relative_data!
expect(relative_url.authority()).to_equal("safe.test")
expect(relative_url.path).to_equal("/dir/next")
expect(relative_url.query).to_equal("return=https://id.test/")
expect(relative_url.request_target()).to_equal(
    "/dir/next?return=https://id.test/"
)

val nbsp = 0xA0.to_char()
val url = Url(
    scheme: "https",
    host: "safe.test",
    port: 443,
    path: "/folder name/" + nbsp + "/%2f/%\r\n",
    query: "q=a b&x=1+2&z=" + nbsp + "&raw=%",
    fragment: "hidden",
    opaque: false
)
val expected = (
    "/folder%20name/%C2%A0/%2f/%25%0D%0A" +
    "?q=a%20b&x=1+2&z=%C2%A0&raw=%25"
)
expect(url.request_target()).to_equal(expected)

step("Serialize the exact target into the HTTP/1.1 request line")
val request = FetchRequest(
    method: "GET",
    url: url,
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "same-origin"
)
expect(build_request_bytes(request)).to_start_with(
    "GET {expected} HTTP/1.1\r\nHost: safe.test\r\n"
)

step("Serialize the exact target into the HTTP/2 path pseudo-header")
val h2_headers = build_h2_headers(request)
expect(h2_headers[3].first).to_equal(":path")
expect(h2_headers[3].second).to_equal(expected)

step("Serialize the exact target into the WebSocket opening handshake")
expect(ws_request_path(url)).to_equal(expected)
expect(build_upgrade_request(
    "safe.test", 443, ws_request_path(url), "key", []
)).to_start_with("GET {expected} HTTP/1.1\r\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `702fa3a68c6e1c400b4921031bb63b715f03fa0f74ec6637ffa28be745730bad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `702fa3a68c6e1c400b4921031bb63b715f03fa0f74ec6637ffa28be745730bad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `702fa3a68c6e1c400b4921031bb63b715f03fa0f74ec6637ffa28be745730bad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/request_target_encoding_security_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should serialize one safe target across HTTP and WebSocket transports' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
