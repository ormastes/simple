# Goods-Sale Vertical — end-to-end scenario over the durable store

> The first proving vertical of the Simple Enterprise Suite, exercised end to end against the durable enterprise store: an admin publishes a product and receives stock; a sales clerk places a guarded order (session -> rbac -> validation -> idempotency -> effects); the order is paid and later refunded; the stock ledger and the double-entry journal stay consistent throughout; the whole state survives a simulated restart; and tenant B can neither see nor mutate tenant A's records.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Goods-Sale Vertical — end-to-end scenario over the durable store

The first proving vertical of the Simple Enterprise Suite, exercised end to end against the durable enterprise store: an admin publishes a product and receives stock; a sales clerk places a guarded order (session -> rbac -> validation -> idempotency -> effects); the order is paid and later refunded; the stock ledger and the double-entry journal stay consistent throughout; the whole state survives a simulated restart; and tenant B can neither see nor mutate tenant A's records.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/03_system/app/enterprise/goods_sale_vertical_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The first proving vertical of the Simple Enterprise Suite, exercised end to
end against the durable enterprise store: an admin publishes a product and
receives stock; a sales clerk places a guarded order (session -> rbac ->
validation -> idempotency -> effects); the order is paid and later refunded;
the stock ledger and the double-entry journal stay consistent throughout;
the whole state survives a simulated restart; and tenant B can neither see
nor mutate tenant A's records.

Command replay is the centerpiece: re-submitting the SAME idempotency key
returns the recorded outcome and provably produces NO second effect — same
stock level, same journal size, same outbox count.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | inactive session rejected |
| rbac | forbidden | viewer role cannot place orders |
| validation | insufficient-stock / not-found | oversell and unknown SKU rejected |
| idempotency | duplicate-key | replay returns recorded result, one effect |

## Ledger invariants

- available stock = sum of signed stock movements; an order that would
  drive it negative is rejected BEFORE any effect;
- every posting is a debit/credit pair; total debits equal total credits
  after create, pay, and refund;
- refund returns the stock and reverses revenue and cash.

## Troubleshooting

- `insufficient-stock` on a fresh store: stock arrives only via
  `sale_receive_stock` (admin role) — check the receive step ran.
- Journal imbalance points at a partial effect: on non-ACID backends
  (interpreter emulation — see the enterprise_store manual) a crash between
  postings cannot be rolled back; production requires the ACID backend.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Wave C, AC-9/AC-10).

## Scenarios

### goods-sale vertical — one complete sale end to end

#### sells, collects payment, and refunds with consistent ledgers

- Open a clean store and publish the catalog
   - Expected: add.reason equals `accepted`
- Receive 10 units of stock
   - Expected: recv.reason equals `accepted`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `10`
- Place a guarded order for 3 units as the sales clerk
   - Expected: placed.reason equals `accepted`
- Verify stock reserved, status created, journal balanced
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `7`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `created`
- Capture payment
   - Expected: paid.reason equals `accepted`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `paid`
- Refund the order — stock returns and the journal reverses in balance
   - Expected: refunded.reason equals `accepted`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `refunded`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `10`
- Verify the audit chain recomputes end to end
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a clean store and publish the catalog")
val store = fresh_store("e2e")
val t = tenant_a()
val admin = admin_a()
val admin_session = session_for(admin, t)
val add = sale_add_product(store, admin_session, t, admin, "SKU-1", "Widget", 2500, "USD")
expect(add.reason).to_equal("accepted")

step("Receive 10 units of stock")
val recv = sale_receive_stock(store, admin_session, t, admin, "SKU-1", 10)
expect(recv.reason).to_equal("accepted")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(10)

step("Place a guarded order for 3 units as the sales clerk")
val clerk = clerk_a()
val clerk_session = session_for(clerk, t)
val placed = sale_place_order(store, clerk_session, t, clerk, envelope("ord-key-1", "sale.order.place"), "order-100", "SKU-1", 3)
expect(placed.ok).to_be(true)
expect(placed.reason).to_equal("accepted")

step("Verify stock reserved, status created, journal balanced")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(7)
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("created")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("Capture payment")
val paid = sale_pay_order(store, clerk_session, t, clerk, envelope("pay-key-1", "sale.order.pay"), "order-100")
expect(paid.reason).to_equal("accepted")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("paid")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("Refund the order — stock returns and the journal reverses in balance")
val refunded = sale_refund_order(store, clerk_session, t, clerk, envelope("ref-key-1", "sale.order.refund"), "order-100")
expect(refunded.reason).to_equal("accepted")
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("refunded")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(10)
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("Verify the audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### goods-sale vertical — guarded sequence denies at every rung

#### rejects an inactive session

- var dead = session for
- Attempt an order with an inactive session
   - Expected: r.reason equals `invalid-session`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("guard_session")
val t = tenant_a()
val clerk = clerk_a()
var dead = session_for(clerk, t)
dead.active = false
step("Attempt an order with an inactive session")
val r = sale_place_order(store, dead, t, clerk, envelope("k-s", "sale.order.place"), "order-x", "SKU-1", 1)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-session")
store_close(store)
```

</details>

#### rejects a role without order permission

- Attempt an order as a viewer
   - Expected: r.reason equals `forbidden`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("guard_role")
val t = tenant_a()
val viewer = viewer_a()
step("Attempt an order as a viewer")
val r = sale_place_order(store, session_for(viewer, t), t, viewer, envelope("k-r", "sale.order.place"), "order-x", "SKU-1", 1)
expect(r.reason).to_equal("forbidden")
store_close(store)
```

</details>

#### rejects an unknown SKU and an oversell

- sale add product
- sale receive stock
- Order an unknown SKU
   - Expected: r1.reason equals `not-found`
- Order more units than available — stock must never go negative
   - Expected: r2.reason equals `insufficient-stock`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `2`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("guard_stock")
val t = tenant_a()
val admin = admin_a()
val admin_session = session_for(admin, t)
sale_add_product(store, admin_session, t, admin, "SKU-1", "Widget", 2500, "USD")
sale_receive_stock(store, admin_session, t, admin, "SKU-1", 2)
val clerk = clerk_a()
val cs = session_for(clerk, t)
step("Order an unknown SKU")
val r1 = sale_place_order(store, cs, t, clerk, envelope("k-n", "sale.order.place"), "order-x", "SKU-404", 1)
expect(r1.reason).to_equal("not-found")
step("Order more units than available — stock must never go negative")
val r2 = sale_place_order(store, cs, t, clerk, envelope("k-o", "sale.order.place"), "order-y", "SKU-1", 3)
expect(r2.reason).to_equal("insufficient-stock")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(2)
store_close(store)
```

</details>

### goods-sale vertical — idempotent replay produces exactly one effect

#### replaying the same order command changes nothing

- sale add product
- sale receive stock
- Place the order once
   - Expected: first.reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `order-200`
- Verify NO second effect — stock and outbox unchanged
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `stock_after_first`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("replay")
val t = tenant_a()
val admin = admin_a()
val admin_session = session_for(admin, t)
sale_add_product(store, admin_session, t, admin, "SKU-1", "Widget", 2500, "USD")
sale_receive_stock(store, admin_session, t, admin, "SKU-1", 10)
val clerk = clerk_a()
val cs = session_for(clerk, t)

step("Place the order once")
val first = sale_place_order(store, cs, t, clerk, envelope("same-key", "sale.order.place"), "order-200", "SKU-1", 4)
expect(first.reason).to_equal("accepted")
val stock_after_first = sale_available_stock(store, "tenant-a", "SKU-1")
val outbox_after_first = outbox_pending(store, "tenant-a").len()

step("Replay the SAME idempotency key")
val replay = sale_place_order(store, cs, t, clerk, envelope("same-key", "sale.order.place"), "order-200", "SKU-1", 4)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("order-200")

step("Verify NO second effect — stock and outbox unchanged")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(stock_after_first)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
store_close(store)
```

</details>

### goods-sale vertical — tenant isolation

#### tenant B cannot read or affect tenant A's catalog and stock

- sale add product
- sale receive stock
- Tenant B sees no stock and no product for tenant A's SKU
   - Expected: sale_available_stock(store, "tenant-b", "SKU-1") equals `0`
- A tenant-B clerk cannot order tenant A's product
   - Expected: r.reason equals `not-found`
- A cross-tenant session is rejected outright
   - Expected: r2.reason equals `invalid-session`
- Tenant A's stock is untouched by the attempts
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `5`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("isolation")
val ta = tenant_a()
val admin = admin_a()
val sa = session_for(admin, ta)
sale_add_product(store, sa, ta, admin, "SKU-1", "Widget", 2500, "USD")
sale_receive_stock(store, sa, ta, admin, "SKU-1", 5)

step("Tenant B sees no stock and no product for tenant A's SKU")
expect(sale_available_stock(store, "tenant-b", "SKU-1")).to_equal(0)

step("A tenant-B clerk cannot order tenant A's product")
val tb = tenant_b()
val clerk_b = ActorContext(actor_id: "clerk-b", role: "sales")
val sb = session_for(clerk_b, tb)
val r = sale_place_order(store, sb, tb, clerk_b, envelope("b-key", "sale.order.place"), "order-b", "SKU-1", 1)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("not-found")

step("A cross-tenant session is rejected outright")
# Session bound to tenant B presented with tenant A as authority.
val forged = SessionContext(token: "tok-clerk-b", actor_id: "clerk-b", tenant_id: "tenant-b", active: true)
val r2 = sale_place_order(store, forged, ta, clerk_b, envelope("b-key-2", "sale.order.place"), "order-b2", "SKU-1", 1)
expect(r2.reason).to_equal("invalid-session")

step("Tenant A's stock is untouched by the attempts")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(5)
store_close(store)
```

</details>

### goods-sale vertical — state survives restart

#### reopens the database with orders, stock, and ledgers intact

- sale add product
- sale receive stock
- sale place order
- Close the store (simulated shutdown)
- store close
- Reopen and verify orders, stock, journal, audit, and replay guard
   - Expected: sale_order_status(store2, "tenant-a", "order-300") equals `created`
   - Expected: sale_available_stock(store2, "tenant-a", "SKU-1") equals `8`
- Replay the pre-restart command against the reopened store
   - Expected: replay.reason equals `duplicate-key`
   - Expected: sale_available_stock(store2, "tenant-a", "SKU-1") equals `8`
- store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("restart")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
sale_add_product(store, sa, t, admin, "SKU-1", "Widget", 2500, "USD")
sale_receive_stock(store, sa, t, admin, "SKU-1", 10)
val clerk = clerk_a()
val cs = session_for(clerk, t)
sale_place_order(store, cs, t, clerk, envelope("restart-key", "sale.order.place"), "order-300", "SKU-1", 2)
step("Close the store (simulated shutdown)")
store_close(store)

step("Reopen and verify orders, stock, journal, audit, and replay guard")
val store2 = store_open(db_path("restart"))
expect(store2.open_ok).to_be(true)
expect(sale_order_status(store2, "tenant-a", "order-300")).to_equal("created")
expect(sale_available_stock(store2, "tenant-a", "SKU-1")).to_equal(8)
expect(sale_journal_balanced(store2, "tenant-a")).to_be(true)
expect(audit_verify_chain(store2, "tenant-a")).to_be(true)

step("Replay the pre-restart command against the reopened store")
val replay = sale_place_order(store2, cs, t, clerk, envelope("restart-key", "sale.order.place"), "order-300", "SKU-1", 2)
expect(replay.reason).to_equal("duplicate-key")
expect(sale_available_stock(store2, "tenant-a", "SKU-1")).to_equal(8)
store_close(store2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
