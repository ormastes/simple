# Enterprise Web App — session issuance and request throttling

> Lane `.spipe/simple_enterprise_suite` W5-A: real login for the enterprise web app. Credentials are per-tenant salted-hash rows seeded via an admin-guarded command (never plaintext); `POST /auth/login` issues a durable session token (sha256 over caller-supplied entropy) and `store_app_handle_bearer` resolves `SessionContext` FROM `Authorization: Bearer <token>` — missing / wrong / revoked / expired all collapse to a GENERIC 401 with no user-enumeration detail. Request throttling is a deterministic fixed-window counter over insert-only rows (caller-supplied `now_epoch`): over-limit -> 429 with the shared security headers, allowed again once the window advances; login attempts get a stricter anti-brute-force window.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Web App — session issuance and request throttling

Lane `.spipe/simple_enterprise_suite` W5-A: real login for the enterprise web app. Credentials are per-tenant salted-hash rows seeded via an admin-guarded command (never plaintext); `POST /auth/login` issues a durable session token (sha256 over caller-supplied entropy) and `store_app_handle_bearer` resolves `SessionContext` FROM `Authorization: Bearer <token>` — missing / wrong / revoked / expired all collapse to a GENERIC 401 with no user-enumeration detail. Request throttling is a deterministic fixed-window counter over insert-only rows (caller-supplied `now_epoch`): over-limit -> 429 with the shared security headers, allowed again once the window advances; login attempts get a stricter anti-brute-force window.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/enterprise_auth_throttle_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Lane `.spipe/simple_enterprise_suite` W5-A: real login for the enterprise web
app. Credentials are per-tenant salted-hash rows seeded via an admin-guarded
command (never plaintext); `POST /auth/login` issues a durable session token
(sha256 over caller-supplied entropy) and `store_app_handle_bearer` resolves
`SessionContext` FROM `Authorization: Bearer <token>` — missing / wrong /
revoked / expired all collapse to a GENERIC 401 with no user-enumeration
detail. Request throttling is a deterministic fixed-window counter over
insert-only rows (caller-supplied `now_epoch`): over-limit -> 429 with the
shared security headers, allowed again once the window advances; login
attempts get a stricter anti-brute-force window.

## Troubleshooting

- Interpreter sqlite caches connections per db PATH — every scenario uses its
  own db path (see `db_path`).
- Token equality across replayed logins is BY DESIGN: the token derives from
  (entropy, tenant, actor, now); same inputs, same token, one extra
  insert-only session row — no divergent effect.
- A 401 body that names the user or distinguishes unknown-user from
  wrong-secret is a defect in the auth route, never in this spec.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W5-A).

## Scenarios

### enterprise auth — login issues a durable bearer session

#### logs in, uses the bearer token, and stays generic on failure

- POST /auth/login with correct credentials returns a token
   - Expected: http_status_code(login.status) equals `200`
- The bearer token authorizes a store route
   - Expected: http_status_code(cat.status) equals `200`
- Wrong secret is a generic 401 — identical to unknown user
   - Expected: http_status_code(wrong.status) equals `401`
   - Expected: http_status_code(ghost.status) equals `401`
   - Expected: wrong.body equals `ghost.body`
- A missing bearer token is 401 on a protected route
   - Expected: http_status_code(anon.status) equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh("login")
val t = tenant_a()

step("POST /auth/login with correct credentials returns a token")
val login = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=1000", 100, "entropy-1")
expect(http_status_code(login.status)).to_equal(200)
expect(login.body.starts_with("token=")).to_be(true)
val token = login.body.slice(6, login.body.len())
expect(token.len() > 30).to_be(true)

step("The bearer token authorizes a store route")
val cat = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 200, "")
expect(http_status_code(cat.status)).to_equal(200)

step("Wrong secret is a generic 401 — identical to unknown user")
val wrong = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=nope", 300, "entropy-2")
expect(http_status_code(wrong.status)).to_equal(401)
val ghost = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=who-is-this&secret=nope", 300, "entropy-3")
expect(http_status_code(ghost.status)).to_equal(401)
expect(wrong.body).to_equal(ghost.body)
expect(wrong.body.contains("clerk-1")).to_be(false)

step("A missing bearer token is 401 on a protected route")
val anon = store_app_handle_bearer(store, t, "GET", "/store/catalog", plain_headers(), "", 400, "")
expect(http_status_code(anon.status)).to_equal(401)
store_close(store)
```

</details>

### enterprise auth — revocation and expiry

#### revoked and expired tokens are 401

- Issue a session with ttl 100 at now=1000
   - Expected: http_status_code(login.status) equals `200`
- Within ttl (now=1050) the token authorizes
   - Expected: http_status_code(ok.status) equals `200`
- At now=1100 (issued_at + ttl) the token is expired — 401
   - Expected: http_status_code(expired.status) equals `401`
- A fresh token revoked via POST /auth/logout is 401 afterwards
   - Expected: http_status_code(out.status) equals `200`
   - Expected: http_status_code(after.status) equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh("expiry")
val t = tenant_a()

step("Issue a session with ttl 100 at now=1000")
val login = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=100", 1000, "entropy-e")
expect(http_status_code(login.status)).to_equal(200)
val token = login.body.slice(6, login.body.len())

step("Within ttl (now=1050) the token authorizes")
val ok = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 1050, "")
expect(http_status_code(ok.status)).to_equal(200)

step("At now=1100 (issued_at + ttl) the token is expired — 401")
val expired = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 1100, "")
expect(http_status_code(expired.status)).to_equal(401)

step("A fresh token revoked via POST /auth/logout is 401 afterwards")
val login2 = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=5000", 1200, "entropy-f")
val token2 = login2.body.slice(6, login2.body.len())
val out = store_app_handle_bearer(store, t, "POST", "/auth/logout", bearer_headers(token2), "", 1210, "")
expect(http_status_code(out.status)).to_equal(200)
val after = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token2), "", 1220, "")
expect(http_status_code(after.status)).to_equal(401)
store_close(store)
```

</details>

### enterprise auth — replayed login idempotency

#### same entropy + now yields the same token, no divergent session

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh("replay")
val t = tenant_a()
val a = session_issue(store, "tenant-a", "clerk-1", "s3cret", 500, 1000, "same-entropy")
val b = session_issue(store, "tenant-a", "clerk-1", "s3cret", 500, 1000, "same-entropy")
expect(a.ok).to_be(true)
expect(b.ok).to_be(true)
expect(a.detail).to_equal(b.detail)
val resolved = session_resolve(store, "tenant-a", a.detail, 600)
expect(resolved.0.active).to_be(true)
expect(resolved.0.actor_id).to_equal("clerk-1")
store_close(store)
```

</details>

### enterprise auth — tenant isolation of sessions

#### a tenant-a token never resolves under tenant-b

- Under tenant-b the same token is 401
   - Expected: http_status_code(cross.status) equals `401`
- Direct resolve under tenant-b is inactive


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh("isolation")
val t = tenant_a()
val login = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=1000", 100, "entropy-i")
val token = login.body.slice(6, login.body.len())

step("Under tenant-b the same token is 401")
val cross = store_app_handle_bearer(store, tenant_b(), "GET", "/store/catalog", bearer_headers(token), "", 200, "")
expect(http_status_code(cross.status)).to_equal(401)

step("Direct resolve under tenant-b is inactive")
val r = session_resolve(store, "tenant-b", token, 200)
expect(r.0.active).to_be(false)
store_close(store)
```

</details>

### enterprise throttle — fixed window with deterministic clock

#### over-limit is 429 with security headers, allowed after the window

- Exhaust the 30-request general window at now=200
   - Expected: last equals `429`
- The 429 carries the shared security-header policy
- Advancing now past the window admits again
   - Expected: http_status_code(next.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh("throttle")
val t = tenant_a()
val login = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=100000", 100, "entropy-t")
val token = login.body.slice(6, login.body.len())

step("Exhaust the 30-request general window at now=200")
var last = 0
var i = 0
while i < 31:
    val r = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 200, "")
    last = http_status_code(r.status)
    i = i + 1
expect(last).to_equal(429)

step("The 429 carries the shared security-header policy")
val over = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 200, "")
var has_cto = false
for h in over.headers:
    if h.0 == "X-Content-Type-Options":
        has_cto = true
expect(has_cto).to_be(true)

step("Advancing now past the window admits again")
val next = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 260, "")
expect(http_status_code(next.status)).to_equal(200)
store_close(store)
```

</details>

### enterprise throttle — login brute force gets the stricter window

#### 5 failed logins lock the 6th attempt (even correct) until the window turns

- 5 wrong-secret logins for clerk-1 at now=100 fill the login window
   - Expected: http_status_code(r.status) equals `401`
- The 6th attempt — even with the CORRECT secret — is 429
   - Expected: http_status_code(locked.status) equals `429`
- A different user is not locked out (per-key window)
   - Expected: http_status_code(other.status) equals `401`
- After the window advances the correct login succeeds
   - Expected: http_status_code(next.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh("brute")
val t = tenant_a()

step("5 wrong-secret logins for clerk-1 at now=100 fill the login window")
var i = 0
while i < 5:
    val r = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
        "user=clerk-1&secret=wrong", 100, "e-{i}")
    expect(http_status_code(r.status)).to_equal(401)
    i = i + 1

step("The 6th attempt — even with the CORRECT secret — is 429")
val locked = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret", 110, "e-lock")
expect(http_status_code(locked.status)).to_equal(429)

step("A different user is not locked out (per-key window)")
val other = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=someone-else&secret=x", 110, "e-other")
expect(http_status_code(other.status)).to_equal(401)

step("After the window advances the correct login succeeds")
val next = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=1000", 170, "e-next")
expect(http_status_code(next.status)).to_equal(200)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>
