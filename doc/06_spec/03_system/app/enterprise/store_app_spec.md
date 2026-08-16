# Store App — customer flow end to end over the hardened route path

> AC-16 of `.spipe/simple_enterprise_suite` (Goal Set v2): the customer-facing store vertical — browse catalog -> cart -> guarded order (`sale_place_order`) -> pay (`sale_pay_order`) -> receipt — dispatched through `store_app_handle`, which routes via `std.common.net.http_core` (`body_decision`, `path_is_safe`, `match_route_pattern`) and executes ONLY the frozen guarded sequence from `std.enterprise_sale`. No new storage, no new guard path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Store App — customer flow end to end over the hardened route path

AC-16 of `.spipe/simple_enterprise_suite` (Goal Set v2): the customer-facing store vertical — browse catalog -> cart -> guarded order (`sale_place_order`) -> pay (`sale_pay_order`) -> receipt — dispatched through `store_app_handle`, which routes via `std.common.net.http_core` (`body_decision`, `path_is_safe`, `match_route_pattern`) and executes ONLY the frozen guarded sequence from `std.enterprise_sale`. No new storage, no new guard path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/store_app_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-16 of `.spipe/simple_enterprise_suite` (Goal Set v2): the customer-facing
store vertical — browse catalog -> cart -> guarded order (`sale_place_order`)
-> pay (`sale_pay_order`) -> receipt — dispatched through
`store_app_handle`, which routes via `std.common.net.http_core`
(`body_decision`, `path_is_safe`, `match_route_pattern`) and executes ONLY
the frozen guarded sequence from `std.enterprise_sale`. No new storage, no
new guard path.

Idempotent replay is proven at the HTTP layer: re-POSTing the same order
form with the same `idem` key returns the recorded result and leaves stock
and order state unchanged — exactly one effect. Tenant isolation is proven
by dispatching with a tenant-B session against tenant-A data.

## Troubleshooting

- 409 `insufficient-stock` on a fresh db: seed stock via
  `sale_receive_stock` (admin role) before ordering.
- Interpreter sqlite caches connections per db PATH — every scenario here
  uses its own db path (see `db_path`).

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, L-B, AC-16).

## Scenarios

### store app — browse, cart, order, pay, receipt

#### carries a customer from catalog to a paid receipt

- Seed the catalog and open a sales-clerk session
- Browse the catalog over GET /store/catalog
   - Expected: http_status_code(catalog.status) equals `200`
- Build a cart of 3 Widgets and price it from the catalog
   - Expected: cart_total_cents(store, "tenant-a", cart) equals `7500`
- Check out — POST /store/order runs the guarded sale_place_order
   - Expected: http_status_code(order.status) equals `200`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `created`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `7`
- Pay — POST /store/pay runs the guarded sale_pay_order
   - Expected: http_status_code(pay.status) equals `200`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `paid`
- View the receipt — GET /store/order/order-100/receipt
   - Expected: http_status_code(receipt.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed the catalog and open a sales-clerk session")
val store = fresh_seeded("e2e")
val t = tenant_a()
val clerk = clerk_a()
val cs = session_for(clerk, t)

step("Browse the catalog over GET /store/catalog")
val catalog = store_app_handle(store, cs, t, clerk, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(catalog.status)).to_equal(200)
expect(catalog.body.contains("Widget")).to_be(true)
expect(catalog.body.contains("2500")).to_be(true)

step("Build a cart of 3 Widgets and price it from the catalog")
var cart = cart_new()
cart = cart_add(cart, "SKU-1", 3)
expect(cart_total_cents(store, "tenant-a", cart)).to_equal(7500)

step("Check out — POST /store/order runs the guarded sale_place_order")
val order = store_app_handle(store, cs, t, clerk, "POST", "/store/order", plain_headers(),
    "order=order-100&sku=SKU-1&qty=3&idem=key-1")
expect(http_status_code(order.status)).to_equal(200)
expect(order.body.contains("accepted")).to_be(true)
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("created")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(7)

step("Pay — POST /store/pay runs the guarded sale_pay_order")
val pay = store_app_handle(store, cs, t, clerk, "POST", "/store/pay", plain_headers(),
    "order=order-100&idem=pay-1")
expect(http_status_code(pay.status)).to_equal(200)
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("paid")

step("View the receipt — GET /store/order/order-100/receipt")
val receipt = store_app_handle(store, cs, t, clerk, "GET", "/store/order/order-100/receipt", plain_headers(), "")
expect(http_status_code(receipt.status)).to_equal(200)
expect(receipt.body.contains("order-100")).to_be(true)
expect(receipt.body.contains("paid")).to_be(true)
store_close(store)
```

</details>

### store app — idempotent replay at the HTTP layer

#### re-POSTing the same order form produces exactly one effect

- Place the order once
   - Expected: http_status_code(first.status) equals `200`
   - Expected: stock_after_first equals `6`
- Replay the identical POST with the same idem key
   - Expected: http_status_code(replay.status) equals `200`
- Stock is unchanged — no second effect
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `stock_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_seeded("replay")
val t = tenant_a()
val clerk = clerk_a()
val cs = session_for(clerk, t)

step("Place the order once")
val first = store_app_handle(store, cs, t, clerk, "POST", "/store/order", plain_headers(),
    "order=order-200&sku=SKU-1&qty=4&idem=same-key")
expect(http_status_code(first.status)).to_equal(200)
val stock_after_first = sale_available_stock(store, "tenant-a", "SKU-1")
expect(stock_after_first).to_equal(6)

step("Replay the identical POST with the same idem key")
val replay = store_app_handle(store, cs, t, clerk, "POST", "/store/order", plain_headers(),
    "order=order-200&sku=SKU-1&qty=4&idem=same-key")
expect(http_status_code(replay.status)).to_equal(200)
expect(replay.body.contains("duplicate-key")).to_be(true)

step("Stock is unchanged — no second effect")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(stock_after_first)
store_close(store)
```

</details>

### store app — tenant isolation through the dispatcher

#### a tenant-B session neither sees nor orders tenant A's goods

- Tenant B's catalog view contains none of tenant A's products
   - Expected: http_status_code(catalog.status) equals `200`
- Tenant B ordering tenant A's SKU is denied not-found (404)
   - Expected: http_status_code(order.status) equals `404`
- Tenant A's stock is untouched
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_seeded("isolation")
val tb = TenantContext(tenant_id: "tenant-b", name: "Beta Retail")
val clerk_b = ActorContext(actor_id: "clerk-b", role: "sales")
val sb = session_for(clerk_b, tb)

step("Tenant B's catalog view contains none of tenant A's products")
val catalog = store_app_handle(store, sb, tb, clerk_b, "GET", "/store/catalog", plain_headers(), "")
expect(http_status_code(catalog.status)).to_equal(200)
expect(catalog.body.contains("Widget")).to_be(false)

step("Tenant B ordering tenant A's SKU is denied not-found (404)")
val order = store_app_handle(store, sb, tb, clerk_b, "POST", "/store/order", plain_headers(),
    "order=order-b&sku=SKU-1&qty=1&idem=b-key")
expect(http_status_code(order.status)).to_equal(404)

step("Tenant A's stock is untouched")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(10)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>
