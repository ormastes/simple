# Browser Fetch bypasses CORS preflight for unsafe request headers

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** high — cross-origin network side effects can occur before denial
- **Verified revision:** `30af808b2eebbfb38cf9f3132869a0e9e2cd26f3`
- **Scope:** shared browser `FetchEngine` and CORS policy

## Exact exploit

A page with requester origin `https://app.test` issues a credential-free CORS
request:

```text
GET https://api.test/admin
X-Admin-Action: delete
```

`GET` is safelisted, while `CorsChecker.needs_preflight` currently examines
only the method and the substring `content-type: application/json`. It ignores
`X-Admin-Action`, so `FetchEngine` sends the actual `GET`. A later CORS response
denial can hide the body from the page but cannot undo an endpoint side effect.

This is not the cookie-name, TLS-verification, mixed-content, HSTS, or HTTP
framing issue tracked elsewhere.

## Existing true OPTIONS owner path

The correct transport path already exists:

1. `FetchEngine.prepare_single_hop` prepares browser-owned request identity and
   calls `FetchEngine.handle_cors_preflight`.
2. `CorsChecker.needs_preflight` decides whether OPTIONS is required.
3. `CorsChecker.create_preflight` constructs the OPTIONS request.
4. `FetchEngine.execute_http` sends it.
5. `CorsChecker.validate_preflight_method_with_credentials` validates origin
   and method before actual transport.

The missing connection is exact unsafe-header discovery/emission and
validation. `CorsChecker.validate_preflight_headers` already exists, but
`FetchEngine.handle_cors_preflight` does not call it. The fix must extend this
real path; rejecting unsafe headers locally would change supported web
semantics and is not accepted.

## Current committed-source evidence

At the verified revision:

- `src/lib/gc_async_mut/gpu/browser_engine/net/cors.spl` has duplicate
  preflight predicates that recognize non-simple methods and JSON content type,
  but not arbitrary non-safelisted author headers.
- `create_preflight` hardcodes
  `Access-Control-Request-Headers: content-type` instead of emitting the exact
  sorted unsafe-name set.
- `src/lib/gc_async_mut/gpu/browser_engine/net/fetch.spl` validates only the
  requested method after OPTIONS.
- `test/unit/browser_engine/net/cors_spec.spl` still expects ACAH `*` to permit
  `authorization`.

## Rejected draft review blockers

A prior uncommitted draft was statically rejected and must not be reused as an
implementation candidate. Any fresh implementation must resolve all four
findings:

1. **ACAM semantics:** a preflight triggered only by headers must allow a
   safelisted GET/HEAD/POST without requiring an explicit ACAM token. ACAM `*`
   covers a noncredentialed non-simple method, but not credentials `include`.
2. **Aggregate safelist ceiling:** unsafe-name discovery must enforce the Fetch
   algorithm's 1,024-byte aggregate limit for otherwise safelisted header
   values, in addition to individual value rules.
3. **No-side-effect oracle:** observing OPTIONS first is insufficient. The
   system oracle must prove exactly one matching request and zero actual GETs.
4. **Authorization wildcard:** ACAH `*` must not authorize `Authorization`;
   reconcile the stale mirrored assertion and require the name explicitly.

## Frozen acceptance

The modern SSpec/manual uses exactly these four visible steps:

1. `Register a cross-origin endpoint that omits X-Admin-Action permission`.
2. `Issue a credential-free CORS GET carrying X-Admin-Action`.
3. `Observe the first and only OPTIONS advertising x-admin-action`.
4. `Reject the fetch before the ungranted action reaches the endpoint`.

Acceptance requires all of the following direct evidence:

- first and only matching transport request is `OPTIONS`;
- `Access-Control-Request-Headers` contains lowercase `x-admin-action`;
- matching `GET` count is zero and Fetch returns preflight denial;
- exactly 1,024 aggregate safelisted value bytes remain below the extra
  preflight boundary, while 1,025 bytes require preflight;
- safelisted-method/no-ACAM and ACAM-wildcard credential cases match the rules
  above; and
- wildcard ACAH permits an ordinary noncredentialed custom header but never
  `Authorization` without an explicit token.

No build, bootstrap, runtime execution, or SPipe PASS is recorded by this
tracking artifact.

## 2026-07-31 bounded source candidate

The candidate keeps the existing real OPTIONS transport path and changes only
three production files:

- `cors.spl` derives the exact sorted unsafe author-header names, enforces the
  per-value and 1,024-byte aggregate safelist limits in UTF-8 bytes (including
  aggregate escalation of `Range`), combines duplicate-name raw lines before
  classification, validates ordered single byte ranges, emits ACRH only when
  needed, and applies credential-aware ACAM/ACAH wildcard rules including the
  explicit `Authorization` exception;
- `fetch.spl` validates both requested method and unsafe names after the
  OPTIONS response and before actual transport; and
- `h1_client.spl` exposes a mock request-count oracle so the focused system
  scenario can prove one OPTIONS and zero GET requests.

The modern focused SSpec/manual and reconciled unit mirrors are included. This
candidate records no build, bootstrap, runtime execution, or SPipe PASS; those
remain pending outside this bounded static lane.
