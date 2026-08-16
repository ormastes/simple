# Enterprise Web App — booking, restaurant, and admin dashboard over the hardened dispatcher

> Lane `.spipe/simple_enterprise_suite` W3-B: the enterprise web app grows the booking (`/booking/*`), restaurant (`/restaurant/*`), and admin dashboard (`GET /admin/dashboard`) route families — all dispatched through the SAME hardened prelude in `store_app_handle` (limits -> `path_is_safe` -> `session_valid` -> route), executing ONLY the frozen guarded commands of `std.enterprise_booking` / `std.enterprise_restaurant`. No new auth scheme, no new storage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Web App — booking, restaurant, and admin dashboard over the hardened dispatcher

Lane `.spipe/simple_enterprise_suite` W3-B: the enterprise web app grows the booking (`/booking/*`), restaurant (`/restaurant/*`), and admin dashboard (`GET /admin/dashboard`) route families — all dispatched through the SAME hardened prelude in `store_app_handle` (limits -> `path_is_safe` -> `session_valid` -> route), executing ONLY the frozen guarded commands of `std.enterprise_booking` / `std.enterprise_restaurant`. No new auth scheme, no new storage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/enterprise_web_app_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Lane `.spipe/simple_enterprise_suite` W3-B: the enterprise web app grows the
booking (`/booking/*`), restaurant (`/restaurant/*`), and admin dashboard
(`GET /admin/dashboard`) route families — all dispatched through the SAME
hardened prelude in `store_app_handle` (limits -> `path_is_safe` ->
`session_valid` -> route), executing ONLY the frozen guarded commands of
`std.enterprise_booking` / `std.enterprise_restaurant`. No new auth scheme,
no new storage.

Frozen denial -> HTTP mapping proven here: `conflict`, `table-occupied`,
`session-closed`, `invalid-transition` -> 409; `no-session` -> 404;
`invalid-session` -> 401 on every new route family. Idempotent replay
through the HTTP layer produces exactly one effect. The dashboard is
read-only, admin-role gated via the frozen `role_allows`, and escapes a
hostile product name.

## Troubleshooting

- Interpreter sqlite caches connections per db PATH — every scenario here
  uses its own db path (see `db_path`).
- Dashboard "Outbox pending" needs `outbox_worker_setup` run once on the
  store (creates the dispatch ledger the pending derivation reads).
- A raw `<script>` in the dashboard body means business data bypassed
  `esc()` — fix the view, never the spec.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W3-B).

## Scenarios

### enterprise web app — booking flow through the hardened dispatcher

#### holds, conflicts with 409, confirms, and cancels over HTTP

- Seed an exclusive-unit resource and open a booking-role session
- List resources over GET /booking/resources
   - Expected: http_status_code(list.status) equals `200`
- Place a hold — POST /booking/hold (digit-checked epochs and ttl)
   - Expected: http_status_code(hold.status) equals `200`
   - Expected: booking_status(store, "tenant-a", "bk-1") equals `hold`
- An overlapping hold on the exclusive unit is denied conflict (409)
   - Expected: http_status_code(clash.status) equals `409`
- Confirm the live hold — POST /booking/confirm
   - Expected: http_status_code(confirm.status) equals `200`
- GET /booking/bk-1/status shows the derived status
   - Expected: http_status_code(status.status) equals `200`
- An unknown booking id is 404 on the status route
   - Expected: http_status_code(missing.status) equals `404`
- Cancel — POST /booking/cancel
   - Expected: http_status_code(cancel.status) equals `200`
   - Expected: booking_status(store, "tenant-a", "bk-1") equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed an exclusive-unit resource and open a booking-role session")
val store = fresh_full("booking")
val t = tenant_a()
val admin = admin_a()
booking_create_resource(store, session_for(admin, t), t, admin, "room-1", "exclusive-unit", 0, "")
val agent = ActorContext(actor_id: "agent-1", role: "booking")
val s = session_for(agent, t)

step("List resources over GET /booking/resources")
val list = store_app_handle(store, s, t, agent, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(list.status)).to_equal(200)
expect(list.body.contains("room-1")).to_be(true)

step("Place a hold — POST /booking/hold (digit-checked epochs and ttl)")
val hold = store_app_handle(store, s, t, agent, "POST", "/booking/hold", plain_headers(),
    "booking=bk-1&resource=room-1&start=100&end=200&qty=1&seat=&now=50&ttl=1000&idem=hold-1")
expect(http_status_code(hold.status)).to_equal(200)
expect(booking_status(store, "tenant-a", "bk-1")).to_equal("hold")

step("An overlapping hold on the exclusive unit is denied conflict (409)")
val clash = store_app_handle(store, s, t, agent, "POST", "/booking/hold", plain_headers(),
    "booking=bk-2&resource=room-1&start=150&end=250&qty=1&seat=&now=50&ttl=1000&idem=hold-2")
expect(http_status_code(clash.status)).to_equal(409)
expect(clash.body.contains("conflict")).to_be(true)

step("Confirm the live hold — POST /booking/confirm")
val confirm = store_app_handle(store, s, t, agent, "POST", "/booking/confirm", plain_headers(),
    "booking=bk-1&now=60&idem=confirm-1")
expect(http_status_code(confirm.status)).to_equal(200)

step("GET /booking/bk-1/status shows the derived status")
val status = store_app_handle(store, s, t, agent, "GET", "/booking/bk-1/status", plain_headers(), "")
expect(http_status_code(status.status)).to_equal(200)
expect(status.body.contains("confirmed")).to_be(true)

step("An unknown booking id is 404 on the status route")
val missing = store_app_handle(store, s, t, agent, "GET", "/booking/nope/status", plain_headers(), "")
expect(http_status_code(missing.status)).to_equal(404)

step("Cancel — POST /booking/cancel")
val cancel = store_app_handle(store, s, t, agent, "POST", "/booking/cancel", plain_headers(),
    "booking=bk-1&idem=cancel-1")
expect(http_status_code(cancel.status)).to_equal(200)
expect(booking_status(store, "tenant-a", "bk-1")).to_equal("cancelled")
store_close(store)
```

</details>

### enterprise web app — idempotent replay at the HTTP layer

#### re-POSTing the same hold form produces exactly one effect

- Place the hold once
   - Expected: http_status_code(first.status) equals `200`
- Replay with the same idem key but a different booking id
   - Expected: http_status_code(replay.status) equals `200`
- No second booking stream exists — exactly one effect
   - Expected: booking_status(store, "tenant-a", "bk-r2") equals ``
   - Expected: booking_status(store, "tenant-a", "bk-r1") equals `hold`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_full("replay")
val t = tenant_a()
val admin = admin_a()
booking_create_resource(store, session_for(admin, t), t, admin, "room-r", "exclusive-unit", 0, "")
val agent = ActorContext(actor_id: "agent-1", role: "booking")
val s = session_for(agent, t)

step("Place the hold once")
val first = store_app_handle(store, s, t, agent, "POST", "/booking/hold", plain_headers(),
    "booking=bk-r1&resource=room-r&start=100&end=200&qty=1&seat=&now=50&ttl=1000&idem=same-key")
expect(http_status_code(first.status)).to_equal(200)

step("Replay with the same idem key but a different booking id")
val replay = store_app_handle(store, s, t, agent, "POST", "/booking/hold", plain_headers(),
    "booking=bk-r2&resource=room-r&start=300&end=400&qty=1&seat=&now=50&ttl=1000&idem=same-key")
expect(http_status_code(replay.status)).to_equal(200)
expect(replay.body.contains("duplicate-key")).to_be(true)

step("No second booking stream exists — exactly one effect")
expect(booking_status(store, "tenant-a", "bk-r2")).to_equal("")
expect(booking_status(store, "tenant-a", "bk-r1")).to_equal("hold")
store_close(store)
```

</details>

### enterprise web app — restaurant flow through the hardened dispatcher

#### opens a table, orders, serves, views, and closes the bill over HTTP

- Seed the menu (sale catalog) and open an admin session
- Open table 7 — POST /restaurant/table/open
   - Expected: http_status_code(open.status) equals `200`
   - Expected: restaurant_session_state(store, "tenant-a", "rs-1") equals `opened`
- Reopening the occupied table is denied table-occupied (409)
   - Expected: http_status_code(reopen.status) equals `409`
- Order a line — POST /restaurant/order/line
   - Expected: http_status_code(line.status) equals `200`
- Serving before the kitchen marks ready is invalid-transition (409)
   - Expected: http_status_code(early.status) equals `409`
- Kitchen ready then served — the forward-only line machine
   - Expected: http_status_code(ready.status) equals `200`
   - Expected: http_status_code(served.status) equals `200`
- View the table session — escaped lines and served total
   - Expected: http_status_code(view.status) equals `200`
- Close the bill — POST /restaurant/bill/close
   - Expected: http_status_code(close.status) equals `200`
   - Expected: restaurant_session_state(store, "tenant-a", "rs-1") equals `closed`
- Ordering onto the closed session is session-closed (409)
   - Expected: http_status_code(late.status) equals `409`
- A view of a free table is no-session (404)
   - Expected: http_status_code(free.status) equals `404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed the menu (sale catalog) and open an admin session")
val store = fresh_full("restaurant")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_add_product(store, s, t, admin, "DISH-1", "Soup", Money(amount_cents: 900, currency: "USD"))
sale_receive_stock(store, s, t, admin, "DISH-1", 10)

step("Open table 7 — POST /restaurant/table/open")
val open = store_app_handle(store, s, t, admin, "POST", "/restaurant/table/open", plain_headers(),
    "session=rs-1&venue=main&table=t7&party=2&idem=open-1")
expect(http_status_code(open.status)).to_equal(200)
expect(restaurant_session_state(store, "tenant-a", "rs-1")).to_equal("opened")

step("Reopening the occupied table is denied table-occupied (409)")
val reopen = store_app_handle(store, s, t, admin, "POST", "/restaurant/table/open", plain_headers(),
    "session=rs-2&venue=main&table=t7&party=4&idem=open-2")
expect(http_status_code(reopen.status)).to_equal(409)
expect(reopen.body.contains("table-occupied")).to_be(true)

step("Order a line — POST /restaurant/order/line")
val line = store_app_handle(store, s, t, admin, "POST", "/restaurant/order/line", plain_headers(),
    "session=rs-1&line=ln-1&sku=DISH-1&qty=2&mods=no-salt&idem=line-1")
expect(http_status_code(line.status)).to_equal(200)

step("Serving before the kitchen marks ready is invalid-transition (409)")
val early = store_app_handle(store, s, t, admin, "POST", "/restaurant/line/served", plain_headers(),
    "session=rs-1&line=ln-1&idem=early-1")
expect(http_status_code(early.status)).to_equal(409)
expect(early.body.contains("invalid-transition")).to_be(true)

step("Kitchen ready then served — the forward-only line machine")
val ready = store_app_handle(store, s, t, admin, "POST", "/restaurant/kitchen/ready", plain_headers(),
    "session=rs-1&line=ln-1&idem=ready-1")
expect(http_status_code(ready.status)).to_equal(200)
val served = store_app_handle(store, s, t, admin, "POST", "/restaurant/line/served", plain_headers(),
    "session=rs-1&line=ln-1&idem=served-1")
expect(http_status_code(served.status)).to_equal(200)

step("View the table session — escaped lines and served total")
val view = store_app_handle(store, s, t, admin, "GET", "/restaurant/session/t7/view", plain_headers(), "")
expect(http_status_code(view.status)).to_equal(200)
expect(view.body.contains("DISH-1")).to_be(true)
expect(view.body.contains("no-salt")).to_be(true)
expect(view.body.contains("1800")).to_be(true)

step("Close the bill — POST /restaurant/bill/close")
val close = store_app_handle(store, s, t, admin, "POST", "/restaurant/bill/close", plain_headers(),
    "session=rs-1&idem=close-1")
expect(http_status_code(close.status)).to_equal(200)
expect(restaurant_session_state(store, "tenant-a", "rs-1")).to_equal("closed")

step("Ordering onto the closed session is session-closed (409)")
val late = store_app_handle(store, s, t, admin, "POST", "/restaurant/order/line", plain_headers(),
    "session=rs-1&line=ln-2&sku=DISH-1&qty=1&mods=&idem=late-1")
expect(http_status_code(late.status)).to_equal(409)
expect(late.body.contains("session-closed")).to_be(true)

step("A view of a free table is no-session (404)")
val free = store_app_handle(store, s, t, admin, "GET", "/restaurant/session/t9/view", plain_headers(), "")
expect(http_status_code(free.status)).to_equal(404)
store_close(store)
```

</details>

### enterprise web app — admin dashboard

#### summarizes per-tenant counts and escapes a hostile product name

- Seed one hostile-named product, an order, a hold, and an open table
   - Expected: http_status_code(order.status) equals `200`
   - Expected: http_status_code(hold.status) equals `200`
   - Expected: http_status_code(open.status) equals `200`
- GET /admin/dashboard as admin shows the per-tenant counts
   - Expected: http_status_code(dash.status) equals `200`
- The hostile product name is escaped, never raw
- A sales-role session is denied the dashboard with 403
   - Expected: http_status_code(denied.status) equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed one hostile-named product, an order, a hold, and an open table")
val store = fresh_full("dashboard")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_add_product(store, s, t, admin, "SKU-X", "<script>alert(1)</script>", Money(amount_cents: 100, currency: "USD"))
sale_receive_stock(store, s, t, admin, "SKU-X", 5)
booking_create_resource(store, s, t, admin, "room-d", "exclusive-unit", 0, "")
val order = store_app_handle(store, s, t, admin, "POST", "/store/order", plain_headers(),
    "order=order-d1&sku=SKU-X&qty=1&idem=d-order")
expect(http_status_code(order.status)).to_equal(200)
val hold = store_app_handle(store, s, t, admin, "POST", "/booking/hold", plain_headers(),
    "booking=bk-d1&resource=room-d&start=100&end=200&qty=1&seat=&now=50&ttl=1000&idem=d-hold")
expect(http_status_code(hold.status)).to_equal(200)
val open = store_app_handle(store, s, t, admin, "POST", "/restaurant/table/open", plain_headers(),
    "session=rs-d1&venue=main&table=t1&party=2&idem=d-open")
expect(http_status_code(open.status)).to_equal(200)

step("GET /admin/dashboard as admin shows the per-tenant counts")
val dash = store_app_handle(store, s, t, admin, "GET", "/admin/dashboard", plain_headers(), "")
expect(http_status_code(dash.status)).to_equal(200)
expect(dash.body.contains("class=\"products\">1</span>")).to_be(true)
expect(dash.body.contains("class=\"orders\">1</span>")).to_be(true)
expect(dash.body.contains("class=\"bookings\">1</span>")).to_be(true)
expect(dash.body.contains("class=\"open-tables\">1</span>")).to_be(true)
expect(dash.body.contains("class=\"outbox-pending\">3</span>")).to_be(true)
expect(dash.body.contains("class=\"audit\">OK</span>")).to_be(true)

step("The hostile product name is escaped, never raw")
expect(dash.body.contains("&lt;script&gt;")).to_be(true)
expect(dash.body.contains("<script>alert")).to_be(false)

step("A sales-role session is denied the dashboard with 403")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val cs = session_for(clerk, t)
val denied = store_app_handle(store, cs, t, clerk, "GET", "/admin/dashboard", plain_headers(), "")
expect(http_status_code(denied.status)).to_equal(403)
store_close(store)
```

</details>

### enterprise web app — unauthenticated denial on every new route family

#### an inactive session gets 401 before any route logic runs

- Booking family — GET /booking/resources is 401
   - Expected: http_status_code(b.status) equals `401`
- Restaurant family — POST /restaurant/table/open is 401
   - Expected: http_status_code(r.status) equals `401`
- Dashboard — GET /admin/dashboard is 401
   - Expected: http_status_code(d.status) equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_full("unauth")
val t = tenant_a()
val admin = admin_a()
val dead = SessionContext(token: "tok-dead", actor_id: admin.actor_id, tenant_id: t.tenant_id, active: false)

step("Booking family — GET /booking/resources is 401")
val b = store_app_handle(store, dead, t, admin, "GET", "/booking/resources", plain_headers(), "")
expect(http_status_code(b.status)).to_equal(401)

step("Restaurant family — POST /restaurant/table/open is 401")
val r = store_app_handle(store, dead, t, admin, "POST", "/restaurant/table/open", plain_headers(),
    "session=rs-u&venue=main&table=t1&party=2&idem=u-1")
expect(http_status_code(r.status)).to_equal(401)

step("Dashboard — GET /admin/dashboard is 401")
val d = store_app_handle(store, dead, t, admin, "GET", "/admin/dashboard", plain_headers(), "")
expect(http_status_code(d.status)).to_equal(401)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>
