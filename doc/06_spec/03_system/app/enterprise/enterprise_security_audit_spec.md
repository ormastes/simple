# Enterprise Suite — Adversarial Security Audit (executable attack specs)

> Lane `.spipe/simple_enterprise_suite` W9-D. This is an ATTACK spec, not a feature spec: every scenario below drives a real attack through the real hardened dispatcher (`store_app_handle` / `store_app_handle_bearer`) or a real guarded command, and asserts the system FAILS CLOSED.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Suite — Adversarial Security Audit (executable attack specs)

Lane `.spipe/simple_enterprise_suite` W9-D. This is an ATTACK spec, not a feature spec: every scenario below drives a real attack through the real hardened dispatcher (`store_app_handle` / `store_app_handle_bearer`) or a real guarded command, and asserts the system FAILS CLOSED.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/enterprise_security_audit_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Enterprise Suite — Adversarial Security Audit (executable attack specs)

## Overview

Lane `.spipe/simple_enterprise_suite` W9-D. This is an ATTACK spec, not a
feature spec: every scenario below drives a real attack through the real
hardened dispatcher (`store_app_handle` / `store_app_handle_bearer`) or a real
guarded command, and asserts the system FAILS CLOSED.

Attack classes probed (see doc/07_guide/app/enterprise/security_posture.md for
the matrix and the residual risks):

1. **Tenant isolation** — a valid tenant-B session must never read tenant-A
   catalog, employees, purchase orders, booking resources, or the dashboard
   roll-up.
2. **Authorization** — a low-privilege (`sales`) role must not reach an
   admin/back-office read or write by picking a different route that shares
   the same underlying command.
3. **Session handling** — revoked and expired bearer tokens stop working
   everywhere; a tenant-A token is inert against tenant-B; and a caller that
   supplies CONSTANT entropy must still not get a token another party can
   derive or collide with.
4. **Injection / escaping** — SQL-ish payloads through form values reach only
   prepared binds; XSS payloads through supplier / employee / resource /
   table names and through denial details render escaped; traversal in a
   route parameter is rejected.
5. **Payment integrity** — a webhook signature must bind the event it
   authorises (provider_ref + kind + event id + tenant), not just the opaque
   payload, and must not cross tenants.
6. **Denial of service** — no unauthenticated route performs unbounded work
   before the request-limit and throttle rungs, AND the throttle itself does
   not get more expensive the harder it is exercised (W12-B).
7. **Form parsing** — a value carrying an encoded separator is decoded once
   and correctly rather than truncated or passed raw, malformed escapes fail
   closed, and none of that weakens the escaping specs (W12-B).
8. **Authorization consistency** — the booking and restaurant read families
   are role-gated like the back-office ones, not open to any authenticated
   session in the tenant (W12-B).

## Troubleshooting

- A 200 where a 401/403/404/409/413/429 is expected means a rung was skipped
  in the dispatcher — fix the dispatcher, NEVER the expectation.
- A raw `<script>` in a body means a view interpolated business data without
  `esc()` — fix the view.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W9-D).

## Scenarios

### attack: tenant isolation — a tenant-B session reads tenant-A data

#### leaks nothing across ANY of the catalog, hcm, proc, booking, dashboard routes

- Verify: leaks nothing across ANY of the catalog, hcm, proc, booking, dashboard routes
- ATTACK: tenant-B admin reads the store catalog
   - Expected: http_status_code(cat.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ATTACK: tenant-B admin reads the HCM roster
   - Expected: http_status_code(emp.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ATTACK: tenant-B admin reads open purchase orders
   - Expected: http_status_code(pos.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ATTACK: tenant-B admin reads bookable resources
   - Expected: http_status_code(res.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ATTACK: tenant-B admin reads the dashboard roll-up
   - Expected: http_status_code(dash.status) equals `200)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: leaks nothing across ANY of the catalog, hcm, proc, booking, dashboard routes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("tenant")
seed_tenant_a(store)
val tb = tenant_b()
val admin_b = admin_of("b")
val sb = session_for(admin_b, tb)

step("ATTACK: tenant-B admin reads the store catalog")
val cat = store_app_handle(store, sb, tb, admin_b, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(cat.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(cat.body.contains("SKU-A-SECRET")).to_be(false)

step("ATTACK: tenant-B admin reads the HCM roster")
val emp = store_app_handle(store, sb, tb, admin_b, "GET", "/hcm/employees", plain_headers(), "")
expect(http_status_code(emp.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(emp.body.contains("EMP-A-SECRET")).to_be(false)
expect(emp.body.contains("Alice Alpha")).to_be(false)

step("ATTACK: tenant-B admin reads open purchase orders")
val pos = store_app_handle(store, sb, tb, admin_b, "GET", "/proc/pos", plain_headers(), "")
expect(http_status_code(pos.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(pos.body.contains("PO-A-SECRET")).to_be(false)
expect(pos.body.contains("Alpha Supply Co")).to_be(false)

step("ATTACK: tenant-B admin reads bookable resources")
val res = store_app_handle(store, sb, tb, admin_b, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(res.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(res.body.contains("RES-A-SECRET")).to_be(false)

step("ATTACK: tenant-B admin reads the dashboard roll-up")
val dash = store_app_handle(store, sb, tb, admin_b, "GET", "/admin/dashboard", plain_headers(), "")
expect(http_status_code(dash.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(dash.body.contains("SKU-A-SECRET")).to_be(false)
expect(dash.body.contains("<span class=\"employees\">0</span>")).to_be(true)
expect(dash.body.contains("<span class=\"open-pos\">0</span>")).to_be(true)
expect(dash.body.contains("<span class=\"products\">0</span>")).to_be(true)
store_close(store)
```

</details>

#### cannot MUTATE tenant-A records from a tenant-B session

- Verify: cannot MUTATE tenant-A records from a tenant-B session
- ATTACK: tenant-B places an order against tenant-A's SKU
   - Expected: http_status_code(order.status) equals `404)  # oracle: pinned constant asserted by this scenario`
- The order did not appear in tenant-A's stream either
   - Expected: sale_order_status(store, "tenant-a", "ORD-X") equals ``
- ATTACK: tenant-B receives against tenant-A's purchase order
- ATTACK: tenant-B clocks in tenant-A's employee


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: cannot MUTATE tenant-A records from a tenant-B session")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("tenant_mutate")
seed_tenant_a(store)
val tb = tenant_b()
val admin_b = admin_of("b")
val sb = session_for(admin_b, tb)

step("ATTACK: tenant-B places an order against tenant-A's SKU")
val order = store_app_handle(store, sb, tb, admin_b, "POST", "/store/order", plain_headers(),
    "order=ORD-X&sku=SKU-A-SECRET&qty=1&idem=k-x")
expect(http_status_code(order.status)).to_equal(404)  # oracle: pinned constant asserted by this scenario

step("The order did not appear in tenant-A's stream either")
expect(sale_order_status(store, "tenant-a", "ORD-X")).to_equal("")

step("ATTACK: tenant-B receives against tenant-A's purchase order")
val recv = store_app_handle(store, sb, tb, admin_b, "POST", "/proc/receive", plain_headers(),
    "po=PO-A-SECRET&qty=5&idem=k-y")
expect(http_status_code(recv.status) != 200).to_be(true)

step("ATTACK: tenant-B clocks in tenant-A's employee")
val clock = store_app_handle(store, sb, tb, admin_b, "POST", "/hcm/clock/in", plain_headers(),
    "employee=EMP-A-SECRET&now=200&idem=k-z")
expect(http_status_code(clock.status) != 200).to_be(true)
store_close(store)
```

</details>

### attack: authorization — a low-privilege role hunts for an unguarded route

#### gets 403 on every back-office read and write it can name

- Verify: gets 403 on every back-office read and write it can name
- ATTACK: the sales clerk reads the admin dashboard
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/admin/dashboard", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the sales clerk reads the HCM roster and payroll export
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/hcm/employees", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/hcm/payroll/export", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the sales clerk reads procurement POs and the reconciliation
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/proc/pos", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/proc/reconcile", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the sales clerk reads every finance report
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/trial-balance", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/ar", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/ap", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/period/status", plain_headers(), "").status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the sales clerk decides a leave request and closes a period
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "POST", "/hcm/leave/decide", plain_headers(), "leave=LV-1&approve=1&idem=k1").status) equals `403)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "POST", "/fin/period/close", plain_headers(), "end=1000&now=1001&idem=k2").status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the sales clerk seeds itself an admin credential via the proc route family
   - Expected: http_status_code(store_app_handle(store, sc, t, clerk, "POST", "/proc/po", plain_headers(), "po=PO-EVIL&req=REQ-A-SECRET&supplier=SUP-A-SECRET&cost=1&idem=k3").status) equals `403)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-X
step("Verify: gets 403 on every back-office read and write it can name")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("authz")
seed_tenant_a(store)
val t = tenant_a()
val clerk = sales_actor()
val sc = session_for(clerk, t)

step("ATTACK: the sales clerk reads the admin dashboard")
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/admin/dashboard", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("ATTACK: the sales clerk reads the HCM roster and payroll export")
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/hcm/employees", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/hcm/payroll/export", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("ATTACK: the sales clerk reads procurement POs and the reconciliation")
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/proc/pos", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/proc/reconcile", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("ATTACK: the sales clerk reads every finance report")
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/trial-balance", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/ar", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/ap", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sc, t, clerk, "GET", "/fin/period/status", plain_headers(), "").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("ATTACK: the sales clerk decides a leave request and closes a period")
expect(http_status_code(store_app_handle(store, sc, t, clerk, "POST", "/hcm/leave/decide", plain_headers(), "leave=LV-1&approve=1&idem=k1").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sc, t, clerk, "POST", "/fin/period/close", plain_headers(), "end=1000&now=1001&idem=k2").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("ATTACK: the sales clerk seeds itself an admin credential via the proc route family")
expect(http_status_code(store_app_handle(store, sc, t, clerk, "POST", "/proc/po", plain_headers(), "po=PO-EVIL&req=REQ-A-SECRET&supplier=SUP-A-SECRET&cost=1&idem=k3").status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
store_close(store)
```

</details>

### attack: session handling — stolen, revoked, expired, cross-tenant tokens

#### refuses a revoked, an expired, and a cross-tenant bearer token

- Verify: refuses a revoked, an expired, and a cross-tenant bearer token
- Log in legitimately
   - Expected: http_status_code(login.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the same token against tenant-B
   - Expected: http_status_code(cross.status) equals `401)  # oracle: pinned constant asserted by this scenario`
- ATTACK: the token after expiry
   - Expected: http_status_code(expired.status) equals `401)  # oracle: pinned constant asserted by this scenario`
- ATTACK: a revoked token, on a write route and on a read route
   - Expected: http_status_code(store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(tok2), "", 1310, "e").status) equals `401)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle_bearer(store, t, "POST", "/store/order", bearer_headers(tok2), "order=O1&sku=S&qty=1&idem=i", 1311, "e").status) equals `401)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle_bearer(store, t, "POST", "/auth/logout", bearer_headers(tok2), "", 1312, "e").status) equals `401)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: refuses a revoked, an expired, and a cross-tenant bearer token")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("session")
val t = tenant_a()
val admin = admin_of("a")
credential_seed(store, session_for(admin, t), t, admin, "clerk-1", "sales", "salt-1", "s3cret")

step("Log in legitimately")
val login = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=100", 1000, "server-entropy-aaaa")
expect(http_status_code(login.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
val token = login.body.replace("token=", "")
expect(token.len() > 0).to_be(true)

step("ATTACK: the same token against tenant-B")
val cross = store_app_handle_bearer(store, tenant_b(), "GET", "/store/catalog", bearer_headers(token), "", 1010, "e")
expect(http_status_code(cross.status)).to_equal(401)  # oracle: pinned constant asserted by this scenario

step("ATTACK: the token after expiry")
val expired = store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(token), "", 1200, "e")
expect(http_status_code(expired.status)).to_equal(401)  # oracle: pinned constant asserted by this scenario

step("ATTACK: a revoked token, on a write route and on a read route")
val login2 = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=s3cret&ttl=1000", 1300, "server-entropy-bbbb")
val tok2 = login2.body.replace("token=", "")
session_revoke(store, "tenant-a", tok2)
expect(http_status_code(store_app_handle_bearer(store, t, "GET", "/store/catalog", bearer_headers(tok2), "", 1310, "e").status)).to_equal(401)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle_bearer(store, t, "POST", "/store/order", bearer_headers(tok2), "order=O1&sku=S&qty=1&idem=i", 1311, "e").status)).to_equal(401)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle_bearer(store, t, "POST", "/auth/logout", bearer_headers(tok2), "", 1312, "e").status)).to_equal(401)  # oracle: pinned constant asserted by this scenario
store_close(store)
```

</details>

#### does not hand out a guessable or colliding token when the caller supplies CONSTANT entropy

- Verify: does not hand out a guessable or colliding token when the caller supplies CONSTANT entropy
- A deployment wires a CONSTANT entropy value (the realistic mistake)
- Two logins for the same actor at the same epoch must not collide
- ATTACK: the attacker knows entropy, tenant, actor and epoch — derive the victim's token
- The victim's live token is not reachable by replaying the derivation inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: does not hand out a guessable or colliding token when the caller supplies CONSTANT entropy")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("token_entropy")
val t = tenant_a()
val admin = admin_of("a")
credential_seed(store, session_for(admin, t), t, admin, "victim", "sales", "salt-v", "victim-secret")
credential_seed(store, session_for(admin, t), t, admin, "attacker", "sales", "salt-x", "attacker-secret")

step("A deployment wires a CONSTANT entropy value (the realistic mistake)")
val fixed = "CONSTANT"

step("Two logins for the same actor at the same epoch must not collide")
val a1 = session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, fixed)
val a2 = session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, fixed)
expect(a1.ok).to_be(true)
expect(a2.ok).to_be(true)
expect(a1.detail == a2.detail).to_be(false)

step("ATTACK: the attacker knows entropy, tenant, actor and epoch — derive the victim's token")
val mine = session_issue(store, "tenant-a", "attacker", "attacker-secret", 5000, 600, fixed)
expect(mine.ok).to_be(true)
expect(mine.detail == a1.detail).to_be(false)
expect(mine.detail == a2.detail).to_be(false)

step("The victim's live token is not reachable by replaying the derivation inputs")
val guess = session_issue(store, "tenant-a", "attacker", "attacker-secret", 5000, 600, fixed)
expect(guess.detail == a1.detail).to_be(false)
store_close(store)
```

</details>

#### rejects entropy too short to have come from a CSPRNG (W13-C boundary check)

- Verify: rejects entropy too short to have come from a CSPRNG (W13-C boundary check)
- The library reads no randomness by design; the deployment feeds it.
- But an EMPTY or sub-8-byte entropy cannot be CSPRNG output — denied
- ...with the same generic denial as a bad credential (no oracle)
   - Expected: session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, "abc").reason equals `invalid-credentials`
- 8 bytes or more passes the boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: rejects entropy too short to have come from a CSPRNG (W13-C boundary check)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("token_entropy_len")
val t = tenant_a()
val admin = admin_of("a")
credential_seed(store, session_for(admin, t), t, admin, "victim", "sales", "salt-v", "victim-secret")

step("The library reads no randomness by design; the deployment feeds it.")
step("But an EMPTY or sub-8-byte entropy cannot be CSPRNG output — denied")
expect(session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, "").ok).to_be(false)
expect(session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, "abc").ok).to_be(false)
expect(session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, "1234567").ok).to_be(false)
step("...with the same generic denial as a bad credential (no oracle)")
expect(session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, "abc").reason).to_equal("invalid-credentials")
step("8 bytes or more passes the boundary")
expect(session_issue(store, "tenant-a", "victim", "victim-secret", 5000, 600, "12345678").ok).to_be(true)
store_close(store)
```

</details>

### attack: injection — SQL-ish payloads, XSS in every rendered field, traversal

#### binds SQL payloads and escapes hostile names on every rendered surface

- Verify: binds SQL payloads and escapes hostile names on every rendered surface
- ATTACK: SQL injection through a form value into a prepared bind
   - Expected: "sqli-not-500=" + "{http_status_code(ord.status) != 500}" equals `sqli-not-500=true`
- The products table still answers reads after the payload
   - Expected: http_status_code(cat.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ATTACK: XSS through the SUPPLIER name
   - Expected: "supplier-raw=" + "{pos.body.contains(\"<script>\")}" equals `supplier-raw=false`
   - Expected: "supplier-esc=" + "{pos.body.contains(\"&lt;script&gt;\")}" equals `supplier-esc=true`
- ATTACK: XSS through the EMPLOYEE name
   - Expected: "employee-raw=" + "{emp.body.contains(\"<script>\")}" equals `employee-raw=false`
   - Expected: "employee-esc=" + "{emp.body.contains(\"&lt;script&gt;\")}" equals `employee-esc=true`
- ATTACK: XSS through the BOOKING RESOURCE id and its seat-map version
- The hostile resource id is accepted as data — the RENDERER must neutralise it
   - Expected: booking_create_resource(store, sa, t, admin, xss, "capacity-pool", 2, "v1").reason equals `accepted`
   - Expected: booking_create_resource(store, sa, t, admin, "RES-X", "capacity-pool", 2, xss).reason equals `accepted`
   - Expected: "resource-raw=" + "{res.body.contains(\"<script>\")}" equals `resource-raw=false`
   - Expected: "resource-listed=" + "{res.body.contains(\"RES-X\")}" equals `resource-listed=true`
   - Expected: "resource-esc=" + "{res.body.contains(\"&lt;script&gt;\")}" equals `resource-esc=true`
- ATTACK: XSS reflected through a DENIAL detail (restaurant table id)
   - Expected: http_status_code(tbl.status) equals `404)  # oracle: pinned constant asserted by this scenario`
   - Expected: "table-raw=" + "{tbl.body.contains(\"<script>\")}" equals `table-raw=false`
- ATTACK: XSS reflected through the receipt route's not-found detail
   - Expected: http_status_code(rcpt.status) equals `404)  # oracle: pinned constant asserted by this scenario`
   - Expected: "receipt-raw=" + "{rcpt.body.contains(\"<script>\")}" equals `receipt-raw=false`
- ATTACK: path traversal via a route parameter, raw and percent-encoded
   - Expected: http_status_code(store_app_handle(store, sa, t, admin, "GET", "/store/order/../../etc/passwd/receipt", plain_headers(), "").status) equals `400)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sa, t, admin, "GET", "/booking/..%2f..%2fetc%2fpasswd/status", plain_headers(), "").status) equals `400)  # oracle: pinned constant asserted by this scenario`
   - Expected: http_status_code(store_app_handle(store, sa, t, admin, "GET", "/hcm/employees%00.png", plain_headers(), "").status) equals `400)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET
step("Verify: binds SQL payloads and escapes hostile names on every rendered surface")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("inject")
val t = tenant_a()
val admin = admin_of("a")
val sa = session_for(admin, t)
val xss = "<script>alert('x')</script>"
val sqli = "'; DROP TABLE products;--"

step("ATTACK: SQL injection through a form value into a prepared bind")
val ord = store_app_handle(store, sa, t, admin, "POST", "/store/order", plain_headers(),
    "order=" + sqli + "&sku=NOPE&qty=1&idem=k-sqli")
expect("sqli-not-500=" + "{http_status_code(ord.status) != 500}").to_equal("sqli-not-500=true")
step("The products table still answers reads after the payload")
val cat = store_app_handle(store, sa, t, admin, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(cat.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario

step("ATTACK: XSS through the SUPPLIER name")
sale_add_product(store, sa, t, admin, "SKU-X", "Plain", Money(amount_cents: 100, currency: "USD"))
proc_supplier_add(store, sa, t, admin, "SUP-X", xss)
proc_requisition_create(store, sa, t, admin, envelope("k-r", "proc.requisition.create"), "REQ-X", "SKU-X", 3)
proc_requisition_approve(store, sa, t, admin, envelope("k-a", "proc.requisition.approve"), "REQ-X")
proc_po_create(store, sa, t, admin, envelope("k-p", "proc.po.create"), "PO-X", "REQ-X", "SUP-X", Money(amount_cents: 10, currency: "USD"))
val pos = store_app_handle(store, sa, t, admin, "GET", "/proc/pos", plain_headers(), "")
expect("supplier-raw=" + "{pos.body.contains(\"<script>\")}").to_equal("supplier-raw=false")
expect("supplier-esc=" + "{pos.body.contains(\"&lt;script&gt;\")}").to_equal("supplier-esc=true")

step("ATTACK: XSS through the EMPLOYEE name")
hcm_hire(store, sa, t, admin, envelope("k-h", "hcm.hire"), "EMP-X", xss, 100, 1000, 40)
val emp = store_app_handle(store, sa, t, admin, "GET", "/hcm/employees", plain_headers(), "")
expect("employee-raw=" + "{emp.body.contains(\"<script>\")}").to_equal("employee-raw=false")
expect("employee-esc=" + "{emp.body.contains(\"&lt;script&gt;\")}").to_equal("employee-esc=true")

step("ATTACK: XSS through the BOOKING RESOURCE id and its seat-map version")
step("The hostile resource id is accepted as data — the RENDERER must neutralise it")
expect(booking_create_resource(store, sa, t, admin, xss, "capacity-pool", 2, "v1").reason).to_equal("accepted")
expect(booking_create_resource(store, sa, t, admin, "RES-X", "capacity-pool", 2, xss).reason).to_equal("accepted")
val res = store_app_handle(store, sa, t, admin, "GET", "/booking/resources", plain_headers(), "")
expect("resource-raw=" + "{res.body.contains(\"<script>\")}").to_equal("resource-raw=false")
expect("resource-listed=" + "{res.body.contains(\"RES-X\")}").to_equal("resource-listed=true")
expect("resource-esc=" + "{res.body.contains(\"&lt;script&gt;\")}").to_equal("resource-esc=true")

step("ATTACK: XSS reflected through a DENIAL detail (restaurant table id)")
val tbl = store_app_handle(store, sa, t, admin, "GET", "/restaurant/session/" + xss + "/view", plain_headers(), "")
expect(http_status_code(tbl.status)).to_equal(404)  # oracle: pinned constant asserted by this scenario
expect("table-raw=" + "{tbl.body.contains(\"<script>\")}").to_equal("table-raw=false")

step("ATTACK: XSS reflected through the receipt route's not-found detail")
val rcpt = store_app_handle(store, sa, t, admin, "GET", "/store/order/" + xss + "/receipt", plain_headers(), "")
expect(http_status_code(rcpt.status)).to_equal(404)  # oracle: pinned constant asserted by this scenario
expect("receipt-raw=" + "{rcpt.body.contains(\"<script>\")}").to_equal("receipt-raw=false")

step("ATTACK: path traversal via a route parameter, raw and percent-encoded")
expect(http_status_code(store_app_handle(store, sa, t, admin, "GET", "/store/order/../../etc/passwd/receipt", plain_headers(), "").status)).to_equal(400)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sa, t, admin, "GET", "/booking/..%2f..%2fetc%2fpasswd/status", plain_headers(), "").status)).to_equal(400)  # oracle: pinned constant asserted by this scenario
expect(http_status_code(store_app_handle(store, sa, t, admin, "GET", "/hcm/employees%00.png", plain_headers(), "").status)).to_equal(400)  # oracle: pinned constant asserted by this scenario
store_close(store)
```

</details>

### attack: payment integrity — webhook signature reuse and cross-tenant replay

#### refuses a valid signature lifted onto a different provider_ref / kind / event

- Verify: refuses a valid signature lifted onto a different provider_ref / kind / event
- Two orders, two pending intents, in the same tenant
- A legitimate capture webhook for intent 1
   - Expected: ok.reason equals `accepted`
   - Expected: payment_intent_status(store, "tenant-a", "INT-1") equals `captured`
- ATTACK: reuse intent 1's payload+signature to capture intent 2
   - Expected: lifted.reason equals `invalid-record`
   - Expected: payment_intent_status(store, "tenant-a", "INT-2") equals `pending`
- ATTACK: reuse the signature with a different event KIND on the same ref
   - Expected: payment_intent_status(store, "tenant-a", "INT-2") equals `pending`
- ATTACK: reuse the signature with a different provider_event_id (dedupe bypass)
- A legacy payload-only signature no longer authorises anything
- ATTACK: replay tenant-A's webhook against tenant-B


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: refuses a valid signature lifted onto a different provider_ref / kind / event")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("payment")
val t = tenant_a()
val admin = admin_of("a")
val sa = session_for(admin, t)
val prov = PaymentProvider(name: "stub", shared_secret: "shhh")

step("Two orders, two pending intents, in the same tenant")
sale_add_product(store, sa, t, admin, "SKU-P", "Payable", Money(amount_cents: 700, currency: "USD"))
sale_receive_stock(store, sa, t, admin, "SKU-P", 10)
sale_place_order(store, sa, t, admin, envelope("k-o1", "sale.order.place"), "ORD-1", "SKU-P", 1)
sale_place_order(store, sa, t, admin, envelope("k-o2", "sale.order.place"), "ORD-2", "SKU-P", 1)
val i1 = payment_create_intent(store, sa, t, admin, envelope("k-i1", "payment.intent.create"), "INT-1", "ORD-1", 100)
val i2 = payment_create_intent(store, sa, t, admin, envelope("k-i2", "payment.intent.create"), "INT-2", "ORD-2", 100)
expect(i1.ok).to_be(true)
expect(i2.ok).to_be(true)

step("A legitimate capture webhook for intent 1")
val payload = "provider=stub&event=captured&ref=" + i1.detail
val sig1 = provider_sign_webhook(prov, "tenant-a", i1.detail, "captured", "evt-1", payload)
val ok = payment_webhook_receive(store, sa, t, admin, wenv("k-w1", payload),
    prov, i1.detail, "captured", sig1, "evt-1", 200)
expect(ok.reason).to_equal("accepted")
expect(payment_intent_status(store, "tenant-a", "INT-1")).to_equal("captured")

step("ATTACK: reuse intent 1's payload+signature to capture intent 2")
val lifted = payment_webhook_receive(store, sa, t, admin, wenv("k-w2", payload),
    prov, i2.detail, "captured", sig1, "evt-2", 210)
expect(lifted.ok).to_be(false)
expect(lifted.reason).to_equal("invalid-record")
expect(payment_intent_status(store, "tenant-a", "INT-2")).to_equal("pending")

step("ATTACK: reuse the signature with a different event KIND on the same ref")
val kind_swap = payment_webhook_receive(store, sa, t, admin, wenv("k-w3", payload),
    prov, i2.detail, "failed", sig1, "evt-3", 220)
expect(kind_swap.ok).to_be(false)
expect(payment_intent_status(store, "tenant-a", "INT-2")).to_equal("pending")

step("ATTACK: reuse the signature with a different provider_event_id (dedupe bypass)")
val id_swap = payment_webhook_receive(store, sa, t, admin, wenv("k-w4", payload),
    prov, i1.detail, "captured", sig1, "evt-99", 230)
expect(id_swap.ok).to_be(false)

step("A legacy payload-only signature no longer authorises anything")
val old_sig = provider_sign(prov, payload)
val legacy = payment_webhook_receive(store, sa, t, admin, wenv("k-w5", payload),
    prov, i2.detail, "captured", old_sig, "evt-5", 240)
expect(legacy.ok).to_be(false)

step("ATTACK: replay tenant-A's webhook against tenant-B")
val tb = tenant_b()
val admin_b = admin_of("b")
val cross = payment_webhook_receive(store, session_for(admin_b, tb), tb, admin_b,
    wenv("k-w6", payload), prov, i1.detail, "captured", sig1, "evt-6", 250)
expect(cross.ok).to_be(false)
store_close(store)
```

</details>

### attack: denial of service — unauthenticated flood and oversized bodies

#### applies the request-limit and throttle rungs to the unauthenticated auth routes

- Verify: applies the request-limit and throttle rungs to the unauthenticated auth routes
- ATTACK: a 20 MB unauthenticated login body
   - Expected: http_status_code(big.status) equals `413)  # oracle: pinned constant asserted by this scenario`
- ATTACK: a smuggling-shaped unauthenticated login (chunked + content-length)
- ATTACK: credential-stuffing flood — rotate the user so the per-user lockout never fires
- The tenant-wide unauthenticated window eventually rejects with 429
   - Expected: codes[codes.len() - 1] equals `429)  # oracle: pinned constant asserted by this scenario`
- A genuine login is still refused generically while the window is saturated


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: applies the request-limit and throttle rungs to the unauthenticated auth routes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("dos")
val t = tenant_a()
val admin = admin_of("a")
credential_seed(store, session_for(admin, t), t, admin, "clerk-1", "sales", "salt-1", "s3cret")

step("ATTACK: a 20 MB unauthenticated login body")
val huge = [("Host", "store.example"), ("Content-Length", "20000000")]
val big = store_app_handle_bearer(store, t, "POST", "/auth/login", huge, "user=clerk-1&secret=s3cret", 100, "ent-1")
expect(http_status_code(big.status)).to_equal(413)  # oracle: pinned constant asserted by this scenario

step("ATTACK: a smuggling-shaped unauthenticated login (chunked + content-length)")
val smuggle = [("Host", "store.example"), ("Content-Length", "10"), ("Transfer-Encoding", "chunked")]
val sm = store_app_handle_bearer(store, t, "POST", "/auth/login", smuggle, "user=clerk-1&secret=s3cret", 100, "ent-2")
expect(http_status_code(sm.status) != 200).to_be(true)

step("ATTACK: credential-stuffing flood — rotate the user so the per-user lockout never fires")
var codes: [i64] = []
var i = 0
while i < 40:
    val r = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
        "user=ghost-" + "{i}" + "&secret=nope", 500, "ent-3")
    codes.push(http_status_code(r.status))
    i = i + 1
step("The tenant-wide unauthenticated window eventually rejects with 429")
expect(codes[codes.len() - 1]).to_equal(429)  # oracle: pinned constant asserted by this scenario

step("A genuine login is still refused generically while the window is saturated")
val gen = store_app_handle_bearer(store, t, "POST", "/auth/login", plain_headers(),
    "user=clerk-1&secret=wrong", 500, "ent-4")
expect(http_status_code(gen.status) == 401 or http_status_code(gen.status) == 429).to_be(true)
store_close(store)
```

</details>

### attack: slow-burn amplification through the throttle's own counter table

#### keeps the count correct across a window boundary AND keeps retained rows bounded

- Verify: keeps the count correct across a window boundary AND keeps retained rows bounded
- Saturate window 0 for one key (limit 3, 60s window)
- The 4th request in the SAME window is rejected
   - Expected: throttle_count(store, "tenant-a|anon", throttle_window(30, 60)) equals `3)  # oracle: pinned constant asserted by this scenario`
- A second key in the same window is counted independently
   - Expected: throttle_count(store, "tenant-a|login:bob", throttle_window(30, 60)) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: throttle_count(store, "tenant-a|anon", throttle_window(30, 60)) equals `3)  # oracle: pinned constant asserted by this scenario`
- Crossing the window boundary re-admits, and the count is the NEW window's
   - Expected: throttle_count(store, "tenant-a|anon", throttle_window(60, 60)) equals `1)  # oracle: pinned constant asserted by this scenario`
- The elapsed window's rows are gone — they can never change a later decision
   - Expected: throttle_count(store, "tenant-a|anon", throttle_window(0, 60)) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: throttle_rows_retained(store) equals `1)  # oracle: pinned constant asserted by this scenario`
- ATTACK: 300 windows of sustained traffic on two rotating keys
- ABSOLUTE ORACLE: retained rows are bounded by the LIVE window, not by total traffic
- ...and the live window still decides correctly on that bounded data
   - Expected: throttle_count(store, "tenant-a|anon", throttle_window(last, 60)) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: keeps the count correct across a window boundary AND keeps retained rows bounded")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("throttle_prune")

step("Saturate window 0 for one key (limit 3, 60s window)")
expect(throttle_admit(store, "tenant-a|anon", 0, 60, 3)).to_be(true)
expect(throttle_admit(store, "tenant-a|anon", 10, 60, 3)).to_be(true)
expect(throttle_admit(store, "tenant-a|anon", 20, 60, 3)).to_be(true)
step("The 4th request in the SAME window is rejected")
expect(throttle_admit(store, "tenant-a|anon", 30, 60, 3)).to_be(false)
expect(throttle_count(store, "tenant-a|anon", throttle_window(30, 60))).to_equal(3)  # oracle: pinned constant asserted by this scenario

step("A second key in the same window is counted independently")
expect(throttle_admit(store, "tenant-a|login:bob", 30, 60, 3)).to_be(true)
expect(throttle_count(store, "tenant-a|login:bob", throttle_window(30, 60))).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(throttle_count(store, "tenant-a|anon", throttle_window(30, 60))).to_equal(3)  # oracle: pinned constant asserted by this scenario

step("Crossing the window boundary re-admits, and the count is the NEW window's")
expect(throttle_admit(store, "tenant-a|anon", 60, 60, 3)).to_be(true)
expect(throttle_count(store, "tenant-a|anon", throttle_window(60, 60))).to_equal(1)  # oracle: pinned constant asserted by this scenario
step("The elapsed window's rows are gone — they can never change a later decision")
expect(throttle_count(store, "tenant-a|anon", throttle_window(0, 60))).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(throttle_rows_retained(store)).to_equal(1)  # oracle: pinned constant asserted by this scenario

step("ATTACK: 300 windows of sustained traffic on two rotating keys")
var w = 2
while w < 302:
    val now = w * 60
    throttle_admit(store, "tenant-a|anon", now, 60, 3)
    throttle_admit(store, "tenant-a|anon", now + 1, 60, 3)
    throttle_admit(store, "tenant-a|login:ghost-" + "{w}", now + 2, 60, 3)
    w = w + 1

step("ABSOLUTE ORACLE: retained rows are bounded by the LIVE window, not by total traffic")
# 900 admits were attempted; unpruned this table would hold ~900 rows.
# Bound: (distinct keys in the live window) * limit = 2 * 3 = 6.
expect(throttle_rows_retained(store) <= 6).to_be(true)
step("...and the live window still decides correctly on that bounded data")
val last = 301 * 60
expect(throttle_count(store, "tenant-a|anon", throttle_window(last, 60))).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(throttle_admit(store, "tenant-a|anon", last + 3, 60, 3)).to_be(true)
expect(throttle_admit(store, "tenant-a|anon", last + 4, 60, 3)).to_be(false)
store_close(store)
```

</details>

### attack: a hostile form value that the old parser truncated or mis-read

#### decodes exactly once and fails closed on every malformed escape

- Verify: decodes exactly once and fails closed on every malformed escape
- Ordinary pairs are unchanged
   - Expected: form_value("a=1&b=2", "b") equals `2`
   - Expected: form_value("a=1", "b") equals ``
   - Expected: form_value("a", "a") equals ``
- A separator INSIDE a value is now expressible (previously truncated to nothing)
   - Expected: form_value("a=x%26y&b=2", "a") equals `x&y`
   - Expected: form_value("a=x%3Dy", "a") equals `x=y`
- An unencoded '=' inside a value splits on the FIRST '=' only
   - Expected: form_value("a=x=y", "a") equals `x=y`
- '+' is a space
   - Expected: form_value("a=hello+world", "a") equals `hello world`
- Decoding happens EXACTLY once — %2526 is the literal %26, never '&'
   - Expected: form_value("a=%2526", "a") equals `%26`
- ATTACK: malformed escapes fail CLOSED, never pass raw
   - Expected: form_value("a=x%2", "a") equals ``
   - Expected: form_value("a=x%", "a") equals ``
   - Expected: form_value("a=x%ZZ", "a") equals ``
- ATTACK: a percent-encoded NUL is rejected outright
   - Expected: form_value("a=x%00y", "a") equals ``
- percent_decode reports the failure explicitly to any other caller
   - Expected: percent_decode("ok%20here").1 equals `ok here`
- Multi-byte UTF-8 escapes decode as BYTES (documented residual: no
- charset recombination) — but never manufacture a '<', '>' or quote
   - Expected: two.1.len() equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: three.1.len() equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: mixed.len() equals `10)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: decodes exactly once and fails closed on every malformed escape")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Ordinary pairs are unchanged")
expect(form_value("a=1&b=2", "b")).to_equal("2")
expect(form_value("a=1", "b")).to_equal("")
expect(form_value("a", "a")).to_equal("")

step("A separator INSIDE a value is now expressible (previously truncated to nothing)")
expect(form_value("a=x%26y&b=2", "a")).to_equal("x&y")
expect(form_value("a=x%3Dy", "a")).to_equal("x=y")
step("An unencoded '=' inside a value splits on the FIRST '=' only")
expect(form_value("a=x=y", "a")).to_equal("x=y")

step("'+' is a space")
expect(form_value("a=hello+world", "a")).to_equal("hello world")

step("Decoding happens EXACTLY once — %2526 is the literal %26, never '&'")
expect(form_value("a=%2526", "a")).to_equal("%26")

step("ATTACK: malformed escapes fail CLOSED, never pass raw")
expect(form_value("a=x%2", "a")).to_equal("")
expect(form_value("a=x%", "a")).to_equal("")
expect(form_value("a=x%ZZ", "a")).to_equal("")
step("ATTACK: a percent-encoded NUL is rejected outright")
expect(form_value("a=x%00y", "a")).to_equal("")

step("percent_decode reports the failure explicitly to any other caller")
expect(percent_decode("ok%20here").0).to_be(true)
expect(percent_decode("ok%20here").1).to_equal("ok here")
expect(percent_decode("bad%2").0).to_be(false)

step("Multi-byte UTF-8 escapes decode as BYTES (documented residual: no")
step("charset recombination) — but never manufacture a '<', '>' or quote")
# 2-byte codepoint: %C3%A9 (é). Decoded byte-wise; both bytes >= 0x80,
# so no markup-significant ASCII can appear from inside the sequence.
val two = percent_decode("caf%C3%A9")
expect(two.0).to_be(true)
expect(two.1.contains("<")).to_be(false)
expect(two.1.contains(">")).to_be(false)
expect(two.1.contains("\"")).to_be(false)
expect(two.1.starts_with("caf")).to_be(true)
# Both decoded bytes must actually be PRESENT (not silently dropped):
# "caf" (3) + 0xC3 0xA9 decoded byte-wise as two chars (4 UTF-8 bytes).
expect(two.1.len()).to_equal(7)  # oracle: pinned constant asserted by this scenario
# 3-byte codepoint: %E2%82%AC (€) — same property.
val three = percent_decode("%E2%82%AC")
expect(three.0).to_be(true)
expect(three.1.contains("<")).to_be(false)
expect(three.1.contains(">")).to_be(false)
expect(three.1.len()).to_equal(6)  # oracle: pinned constant asserted by this scenario
# A multi-byte value with a REAL encoded '<' after it: the '<' comes
# only from its own %3C escape and is visible to the escaper.
val mixed = form_value("a=caf%C3%A9%3Cb%3E", "a")
expect(mixed.contains("<b>")).to_be(true)
expect(mixed.len()).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(esc(mixed).contains("<")).to_be(false)
expect(esc(mixed).contains("&lt;b&gt;")).to_be(true)
```

</details>

#### does NOT weaken escaping: a decoded XSS payload still renders escaped

- Verify: does NOT weaken escaping: a decoded XSS payload still renders escaped
- ATTACK: an XSS payload smuggled through percent-encoding in a form value
- The parser now sees the real payload rather than a truncated fragment
   - Expected: form_value(encoded, "booking") equals `<script>alert(1)</script>`
- ...and the surface that reflects it still escapes it


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: does NOT weaken escaping: a decoded XSS payload still renders escaped")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("form_xss")
val t = tenant_a()
val admin = admin_of("a")
val sa = session_for(admin, t)

step("ATTACK: an XSS payload smuggled through percent-encoding in a form value")
val encoded = "booking=%3Cscript%3Ealert%281%29%3C%2Fscript%3E&idem=k-xss"
step("The parser now sees the real payload rather than a truncated fragment")
expect(form_value(encoded, "booking")).to_equal("<script>alert(1)</script>")
val res = store_app_handle(store, sa, t, admin, "POST", "/booking/cancel", plain_headers(), encoded)
step("...and the surface that reflects it still escapes it")
expect(res.body.contains("<script>")).to_be(false)
expect(res.body.contains("&lt;script&gt;")).to_be(true)
store_close(store)
```

</details>

### attack: a low-privilege session reads the booking and restaurant families

#### role-gates /booking/* and /restaurant/* reads with each family's own frozen action

- Verify: role-gates /booking/* and /restaurant/* reads with each family's own frozen action
- ATTACK: a `sales` session enumerates the tenant's bookable resources
   - Expected: http_status_code(r1.status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: a `sales` session probes a booking id
   - Expected: http_status_code(r2.status) equals `403)  # oracle: pinned constant asserted by this scenario`
- ATTACK: a `sales` session walks table ids to read open bills
   - Expected: http_status_code(r3.status) equals `403)  # oracle: pinned constant asserted by this scenario`
- The `booking` role — which already holds booking.hold — still reads its own family
   - Expected: http_status_code(ok1.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- ...but the booking role does NOT reach the restaurant bill view
   - Expected: http_status_code(r4.status) equals `403)  # oracle: pinned constant asserted by this scenario`
- admin still reaches both — the gate is role_allows, not a new scheme
   - Expected: http_status_code(a1.status) equals `200)  # oracle: pinned constant asserted by this scenario`
- no active session at t7 -> 404, i.e. it passed the role gate
   - Expected: http_status_code(a2.status) equals `404)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-A-SECRET REQ-X
step("Verify: role-gates /booking/* and /restaurant/* reads with each family's own frozen action")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val store = fresh_full("family_rbac")
seed_tenant_a(store)
val t = tenant_a()
val admin = admin_of("a")
val clerk = sales_actor()
val agent = booking_actor()

step("ATTACK: a `sales` session enumerates the tenant's bookable resources")
val r1 = store_app_handle(store, session_for(clerk, t), t, clerk, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(r1.status)).to_equal(403)  # oracle: pinned constant asserted by this scenario
expect(r1.body.contains("RES-A-SECRET")).to_be(false)

step("ATTACK: a `sales` session probes a booking id")
val r2 = store_app_handle(store, session_for(clerk, t), t, clerk, "GET", "/booking/bk-1/status", plain_headers(), "")
expect(http_status_code(r2.status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("ATTACK: a `sales` session walks table ids to read open bills")
val r3 = store_app_handle(store, session_for(clerk, t), t, clerk, "GET", "/restaurant/session/t7/view", plain_headers(), "")
expect(http_status_code(r3.status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("The `booking` role — which already holds booking.hold — still reads its own family")
val ok1 = store_app_handle(store, session_for(agent, t), t, agent, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(ok1.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(ok1.body.contains("RES-A-SECRET")).to_be(true)

step("...but the booking role does NOT reach the restaurant bill view")
val r4 = store_app_handle(store, session_for(agent, t), t, agent, "GET", "/restaurant/session/t7/view", plain_headers(), "")
expect(http_status_code(r4.status)).to_equal(403)  # oracle: pinned constant asserted by this scenario

step("admin still reaches both — the gate is role_allows, not a new scheme")
val a1 = store_app_handle(store, session_for(admin, t), t, admin, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(a1.status)).to_equal(200)  # oracle: pinned constant asserted by this scenario
val a2 = store_app_handle(store, session_for(admin, t), t, admin, "GET", "/restaurant/session/t7/view", plain_headers(), "")
step("no active session at t7 -> 404, i.e. it passed the role gate")
expect(http_status_code(a2.status)).to_equal(404)  # oracle: pinned constant asserted by this scenario
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c0d6633b175e89bd6280abce1d2191da14dacabfe84b4aedb207d7a18bfbca3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c0d6633b175e89bd6280abce1d2191da14dacabfe84b4aedb207d7a18bfbca3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c0d6633b175e89bd6280abce1d2191da14dacabfe84b4aedb207d7a18bfbca3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/enterprise/enterprise_security_audit_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/enterprise_security_audit_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/enterprise_security_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/enterprise_security_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
