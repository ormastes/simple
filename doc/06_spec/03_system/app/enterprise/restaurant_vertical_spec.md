# Restaurant Table-Service Vertical — end-to-end scenario over the durable store

> The table-service proving vertical of the Simple Enterprise Suite, exercised end to end against the durable enterprise store: a host opens a table session; a server orders two rounds of menu lines (the menu IS the sale catalog — a line references a product sku and snapshots its price at line time); the kitchen marks lines ready; the server marks them served; the bill closes the session, posting a balanced cash/revenue journal pair; the whole state survives a simulated restart; and tenant B can neither see nor mutate tenant A's tables.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Restaurant Table-Service Vertical — end-to-end scenario over the durable store

The table-service proving vertical of the Simple Enterprise Suite, exercised end to end against the durable enterprise store: a host opens a table session; a server orders two rounds of menu lines (the menu IS the sale catalog — a line references a product sku and snapshots its price at line time); the kitchen marks lines ready; the server marks them served; the bill closes the session, posting a balanced cash/revenue journal pair; the whole state survives a simulated restart; and tenant B can neither see nor mutate tenant A's tables.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/03_system/app/enterprise/restaurant_vertical_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The table-service proving vertical of the Simple Enterprise Suite, exercised
end to end against the durable enterprise store: a host opens a table
session; a server orders two rounds of menu lines (the menu IS the sale
catalog — a line references a product sku and snapshots its price at line
time); the kitchen marks lines ready; the server marks them served; the bill
closes the session, posting a balanced cash/revenue journal pair; the whole
state survives a simulated restart; and tenant B can neither see nor mutate
tenant A's tables.

The line state machine is forward-only — `ordered -> ready -> served`, with
`voided` allowed from `ordered`/`ready` — and every invalid transition is
denied with the frozen reason `invalid-transition` and provably no effect.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | cross-tenant session rejected |
| rbac | forbidden | viewer role cannot open a table |
| validation | table-occupied / invalid-transition / session-closed / unserved-lines | double-open, out-of-order kitchen flow, post-close order, premature bill |
| idempotency | duplicate-key | replayed order line = exactly one effect |

## Ledger invariants

- a session bills exactly the sum of price-snapshot x qty over its SERVED
  lines; voided lines bill nothing and do not block closing;
- the bill posts one debit/credit pair (cash / sales_revenue); total debits
  equal total credits after close (`sale_journal_balanced`);
- a closed session denies further lines (`session-closed`).

## Troubleshooting

- `table-occupied` on a fresh table: the active-session derivation follows
  the newest `opened` event — check a previous scenario reused the db path
  (each scenario must use its OWN database file).
- `not-found` on order_add_line: menu items are sale-catalog products;
  publish the sku via `sale_add_product` first.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W2-E, §7.3/§7.4 restaurant vertical).

## Scenarios

### restaurant vertical — one full table service end to end

#### opens, orders two rounds, serves, and closes a balanced bill

- Open a clean store and seat a party of 2 at table T1
   - Expected: opened.reason equals `accepted`
   - Expected: restaurant_table_session(store, "tenant-a", "venue-1", "T1") equals `sess-1`
- Round 1: order soup x2 with a modifier — price snapshotted from the menu
   - Expected: l1.reason equals `accepted`
   - Expected: restaurant_line_status(store, "tenant-a", "sess-1", "line-1") equals `ordered`
- Round 2: order one steak
   - Expected: l2.reason equals `accepted`
- Kitchen marks both lines ready, server serves both
   - Expected: kitchen_mark_ready(store, hs, t, host, envelope("r-1", "restaurant.kitchen.ready"), "sess-1", "line-1").reason equals `accepted`
   - Expected: kitchen_mark_ready(store, hs, t, host, envelope("r-2", "restaurant.kitchen.ready"), "sess-1", "line-2").reason equals `accepted`
   - Expected: line_mark_served(store, hs, t, host, envelope("s-1", "restaurant.line.serve"), "sess-1", "line-1").reason equals `accepted`
   - Expected: line_mark_served(store, hs, t, host, envelope("s-2", "restaurant.line.serve"), "sess-1", "line-2").reason equals `accepted`
   - Expected: restaurant_line_status(store, "tenant-a", "sess-1", "line-2") equals `served`
- Close the bill — 2x900 + 1x3400 = 5200, journal balanced
   - Expected: restaurant_session_total(store, "tenant-a", "sess-1") equals `5200`
   - Expected: closed.detail equals `5200`
   - Expected: restaurant_session_state(store, "tenant-a", "sess-1") equals `closed`
- The table is free again and a late line is denied session-closed
   - Expected: restaurant_table_session(store, "tenant-a", "venue-1", "T1") equals ``
   - Expected: late.reason equals `session-closed`
- Verify the audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a clean store and seat a party of 2 at table T1")
val store = fresh_store("e2e")
val t = tenant_a()
val host = host_a()
val hs = session_for(host, t)
val opened = table_open_session(store, hs, t, host, envelope("open-1", "restaurant.table.open"), "sess-1", "venue-1", "T1", 2)
expect(opened.reason).to_equal("accepted")
expect(restaurant_table_session(store, "tenant-a", "venue-1", "T1")).to_equal("sess-1")

step("Round 1: order soup x2 with a modifier — price snapshotted from the menu")
val l1 = order_add_line(store, hs, t, host, envelope("line-1", "restaurant.order.add"), "sess-1", "line-1", "MENU-SOUP", 2, "no croutons")
expect(l1.reason).to_equal("accepted")
expect(restaurant_line_status(store, "tenant-a", "sess-1", "line-1")).to_equal("ordered")

step("Round 2: order one steak")
val l2 = order_add_line(store, hs, t, host, envelope("line-2", "restaurant.order.add"), "sess-1", "line-2", "MENU-STEAK", 1, "medium rare")
expect(l2.reason).to_equal("accepted")

step("Kitchen marks both lines ready, server serves both")
expect(kitchen_mark_ready(store, hs, t, host, envelope("r-1", "restaurant.kitchen.ready"), "sess-1", "line-1").reason).to_equal("accepted")
expect(kitchen_mark_ready(store, hs, t, host, envelope("r-2", "restaurant.kitchen.ready"), "sess-1", "line-2").reason).to_equal("accepted")
expect(line_mark_served(store, hs, t, host, envelope("s-1", "restaurant.line.serve"), "sess-1", "line-1").reason).to_equal("accepted")
expect(line_mark_served(store, hs, t, host, envelope("s-2", "restaurant.line.serve"), "sess-1", "line-2").reason).to_equal("accepted")
expect(restaurant_line_status(store, "tenant-a", "sess-1", "line-2")).to_equal("served")

step("Close the bill — 2x900 + 1x3400 = 5200, journal balanced")
expect(restaurant_session_total(store, "tenant-a", "sess-1")).to_equal(5200)
val closed = bill_close_session(store, hs, t, host, envelope("close-1", "restaurant.bill.close"), "sess-1")
expect(closed.ok).to_be(true)
expect(closed.detail).to_equal("5200")
expect(restaurant_session_state(store, "tenant-a", "sess-1")).to_equal("closed")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("The table is free again and a late line is denied session-closed")
expect(restaurant_table_session(store, "tenant-a", "venue-1", "T1")).to_equal("")
val late = order_add_line(store, hs, t, host, envelope("line-late", "restaurant.order.add"), "sess-1", "line-3", "MENU-SOUP", 1, "")
expect(late.ok).to_be(false)
expect(late.reason).to_equal("session-closed")

step("Verify the audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### restaurant vertical — guarded denials

#### denies opening a table that already has an active session

- Open T1 once
   - Expected: table_open_session(store, hs, t, host, envelope("do-1", "restaurant.table.open"), "sess-a", "venue-1", "T1", 2).reason equals `accepted`
- A second open of the SAME table is denied table-occupied
   - Expected: again.reason equals `table-occupied`
- A different table opens fine
   - Expected: table_open_session(store, hs, t, host, envelope("do-3", "restaurant.table.open"), "sess-c", "venue-1", "T2", 4).reason equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("double_open")
val t = tenant_a()
val host = host_a()
val hs = session_for(host, t)
step("Open T1 once")
expect(table_open_session(store, hs, t, host, envelope("do-1", "restaurant.table.open"), "sess-a", "venue-1", "T1", 2).reason).to_equal("accepted")
step("A second open of the SAME table is denied table-occupied")
val again = table_open_session(store, hs, t, host, envelope("do-2", "restaurant.table.open"), "sess-b", "venue-1", "T1", 4)
expect(again.ok).to_be(false)
expect(again.reason).to_equal("table-occupied")
step("A different table opens fine")
expect(table_open_session(store, hs, t, host, envelope("do-3", "restaurant.table.open"), "sess-c", "venue-1", "T2", 4).reason).to_equal("accepted")
store_close(store)
```

</details>

#### denies invalid line state transitions — the machine is forward-only

- Serving an ordered-but-not-ready line is denied
   - Expected: early.reason equals `invalid-transition`
   - Expected: restaurant_line_status(store, "tenant-a", "sess-1", "line-1") equals `ordered`
- ready then a SECOND ready is denied
   - Expected: kitchen_mark_ready(store, hs, t, host, envelope("tr-r1", "restaurant.kitchen.ready"), "sess-1", "line-1").reason equals `accepted`
   - Expected: reready.reason equals `invalid-transition`
- serve then void-after-serve is denied
   - Expected: line_mark_served(store, hs, t, host, envelope("tr-s2", "restaurant.line.serve"), "sess-1", "line-1").reason equals `accepted`
   - Expected: voided.reason equals `invalid-transition`
- an unknown line is line-not-found, a viewer is forbidden
   - Expected: kitchen_mark_ready(store, hs, t, host, envelope("tr-r3", "restaurant.kitchen.ready"), "sess-1", "line-404").reason equals `line-not-found`
   - Expected: table_open_session(store, session_for(viewer, t), t, viewer, envelope("tr-vw", "restaurant.table.open"), "sess-x", "venue-1", "T9", 2).reason equals `forbidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("transitions")
val t = tenant_a()
val host = host_a()
val hs = session_for(host, t)
table_open_session(store, hs, t, host, envelope("tr-open", "restaurant.table.open"), "sess-1", "venue-1", "T1", 2)
order_add_line(store, hs, t, host, envelope("tr-line", "restaurant.order.add"), "sess-1", "line-1", "MENU-SOUP", 1, "")
step("Serving an ordered-but-not-ready line is denied")
val early = line_mark_served(store, hs, t, host, envelope("tr-s1", "restaurant.line.serve"), "sess-1", "line-1")
expect(early.ok).to_be(false)
expect(early.reason).to_equal("invalid-transition")
expect(restaurant_line_status(store, "tenant-a", "sess-1", "line-1")).to_equal("ordered")
step("ready then a SECOND ready is denied")
expect(kitchen_mark_ready(store, hs, t, host, envelope("tr-r1", "restaurant.kitchen.ready"), "sess-1", "line-1").reason).to_equal("accepted")
val reready = kitchen_mark_ready(store, hs, t, host, envelope("tr-r2", "restaurant.kitchen.ready"), "sess-1", "line-1")
expect(reready.reason).to_equal("invalid-transition")
step("serve then void-after-serve is denied")
expect(line_mark_served(store, hs, t, host, envelope("tr-s2", "restaurant.line.serve"), "sess-1", "line-1").reason).to_equal("accepted")
val voided = order_void_line(store, hs, t, host, envelope("tr-v1", "restaurant.line.void"), "sess-1", "line-1")
expect(voided.reason).to_equal("invalid-transition")
step("an unknown line is line-not-found, a viewer is forbidden")
expect(kitchen_mark_ready(store, hs, t, host, envelope("tr-r3", "restaurant.kitchen.ready"), "sess-1", "line-404").reason).to_equal("line-not-found")
val viewer = viewer_a()
expect(table_open_session(store, session_for(viewer, t), t, viewer, envelope("tr-vw", "restaurant.table.open"), "sess-x", "venue-1", "T9", 2).reason).to_equal("forbidden")
store_close(store)
```

</details>

#### denies closing a bill while unserved lines remain — unless voided

- Closing with line-2 still ordered is denied unserved-lines
   - Expected: premature.reason equals `unserved-lines`
- Void line-2 — the bill closes on the served soup alone
   - Expected: order_void_line(store, hs, t, host, envelope("us-v1", "restaurant.line.void"), "sess-1", "line-2").reason equals `accepted`
   - Expected: closed.reason equals `accepted`
   - Expected: closed.detail equals `900`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("unserved")
val t = tenant_a()
val host = host_a()
val hs = session_for(host, t)
table_open_session(store, hs, t, host, envelope("us-open", "restaurant.table.open"), "sess-1", "venue-1", "T1", 2)
order_add_line(store, hs, t, host, envelope("us-l1", "restaurant.order.add"), "sess-1", "line-1", "MENU-SOUP", 1, "")
order_add_line(store, hs, t, host, envelope("us-l2", "restaurant.order.add"), "sess-1", "line-2", "MENU-STEAK", 1, "")
kitchen_mark_ready(store, hs, t, host, envelope("us-r1", "restaurant.kitchen.ready"), "sess-1", "line-1")
line_mark_served(store, hs, t, host, envelope("us-s1", "restaurant.line.serve"), "sess-1", "line-1")
step("Closing with line-2 still ordered is denied unserved-lines")
val premature = bill_close_session(store, hs, t, host, envelope("us-c1", "restaurant.bill.close"), "sess-1")
expect(premature.ok).to_be(false)
expect(premature.reason).to_equal("unserved-lines")
step("Void line-2 — the bill closes on the served soup alone")
expect(order_void_line(store, hs, t, host, envelope("us-v1", "restaurant.line.void"), "sess-1", "line-2").reason).to_equal("accepted")
val closed = bill_close_session(store, hs, t, host, envelope("us-c2", "restaurant.bill.close"), "sess-1")
expect(closed.reason).to_equal("accepted")
expect(closed.detail).to_equal("900")
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### restaurant vertical — idempotent replay produces exactly one effect

#### replaying the same order-line command changes nothing

- Order the line once
   - Expected: first.reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `line-1`
- Verify NO second effect — outbox unchanged, still one line
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`
   - Expected: restaurant_session_total(store, "tenant-a", "sess-1") equals `total_after_first`
   - Expected: restaurant_line_status(store, "tenant-a", "sess-1", "line-1") equals `ordered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("replay")
val t = tenant_a()
val host = host_a()
val hs = session_for(host, t)
table_open_session(store, hs, t, host, envelope("rp-open", "restaurant.table.open"), "sess-1", "venue-1", "T1", 2)
step("Order the line once")
val first = order_add_line(store, hs, t, host, envelope("same-key", "restaurant.order.add"), "sess-1", "line-1", "MENU-SOUP", 2, "extra bread")
expect(first.reason).to_equal("accepted")
val total_after_first = restaurant_session_total(store, "tenant-a", "sess-1")
val outbox_after_first = outbox_pending(store, "tenant-a").len()
step("Replay the SAME idempotency key")
val replay = order_add_line(store, hs, t, host, envelope("same-key", "restaurant.order.add"), "sess-1", "line-1", "MENU-SOUP", 2, "extra bread")
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("line-1")
step("Verify NO second effect — outbox unchanged, still one line")
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
expect(restaurant_session_total(store, "tenant-a", "sess-1")).to_equal(total_after_first)
expect(restaurant_line_status(store, "tenant-a", "sess-1", "line-1")).to_equal("ordered")
store_close(store)
```

</details>

### restaurant vertical — tenant isolation

#### tenant B cannot see or mutate tenant A's tables and menu

- Tenant B sees the table as free and the session as unknown
   - Expected: restaurant_table_session(store, "tenant-b", "venue-1", "T1") equals ``
   - Expected: restaurant_session_state(store, "tenant-b", "sess-a") equals ``
- A tenant-B host cannot order tenant A's menu item
   - Expected: r.reason equals `not-found`
- A cross-tenant session is rejected outright
   - Expected: r2.reason equals `invalid-session`
- Tenant A's session is untouched by the attempts
   - Expected: restaurant_table_session(store, "tenant-a", "venue-1", "T1") equals `sess-a`
   - Expected: restaurant_session_total(store, "tenant-a", "sess-a") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("isolation")
val ta = tenant_a()
val host = host_a()
val hs = session_for(host, ta)
table_open_session(store, hs, ta, host, envelope("iso-open", "restaurant.table.open"), "sess-a", "venue-1", "T1", 2)
step("Tenant B sees the table as free and the session as unknown")
expect(restaurant_table_session(store, "tenant-b", "venue-1", "T1")).to_equal("")
expect(restaurant_session_state(store, "tenant-b", "sess-a")).to_equal("")
step("A tenant-B host cannot order tenant A's menu item")
val tb = tenant_b()
val host_b = ActorContext(actor_id: "host-b", role: "admin")
val sb = session_for(host_b, tb)
table_open_session(store, sb, tb, host_b, envelope("iso-open-b", "restaurant.table.open"), "sess-b", "venue-1", "T1", 2)
val r = order_add_line(store, sb, tb, host_b, envelope("iso-line-b", "restaurant.order.add"), "sess-b", "line-1", "MENU-SOUP", 1, "")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("not-found")
step("A cross-tenant session is rejected outright")
val forged = SessionContext(token: "tok-host-b", actor_id: "host-b", tenant_id: "tenant-b", active: true)
val r2 = order_add_line(store, forged, ta, host_b, envelope("iso-forged", "restaurant.order.add"), "sess-a", "line-x", "MENU-SOUP", 1, "")
expect(r2.reason).to_equal("invalid-session")
step("Tenant A's session is untouched by the attempts")
expect(restaurant_table_session(store, "tenant-a", "venue-1", "T1")).to_equal("sess-a")
expect(restaurant_session_total(store, "tenant-a", "sess-a")).to_equal(0)
store_close(store)
```

</details>

### restaurant vertical — state survives restart

#### reopens the database with sessions, lines, and replay guard intact

- Close the store (simulated shutdown)
- Reopen and verify session, line state, and audit chain
   - Expected: restaurant_table_session(store2, "tenant-a", "venue-1", "T1") equals `sess-1`
   - Expected: restaurant_line_status(store2, "tenant-a", "sess-1", "line-1") equals `ready`
- Replay the pre-restart order line against the reopened store
   - Expected: replay.reason equals `duplicate-key`
- Finish the service after the restart — served, billed, balanced
   - Expected: line_mark_served(store2, hs, t, host, envelope("rs-serve", "restaurant.line.serve"), "sess-1", "line-1").reason equals `accepted`
   - Expected: closed.detail equals `3400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("restart")
val t = tenant_a()
val host = host_a()
val hs = session_for(host, t)
table_open_session(store, hs, t, host, envelope("rs-open", "restaurant.table.open"), "sess-1", "venue-1", "T1", 2)
order_add_line(store, hs, t, host, envelope("rs-line", "restaurant.order.add"), "sess-1", "line-1", "MENU-STEAK", 1, "")
kitchen_mark_ready(store, hs, t, host, envelope("rs-ready", "restaurant.kitchen.ready"), "sess-1", "line-1")
step("Close the store (simulated shutdown)")
store_close(store)

step("Reopen and verify session, line state, and audit chain")
val store2 = store_open(db_path("restart"))
expect(store2.open_ok).to_be(true)
expect(restaurant_table_session(store2, "tenant-a", "venue-1", "T1")).to_equal("sess-1")
expect(restaurant_line_status(store2, "tenant-a", "sess-1", "line-1")).to_equal("ready")
expect(audit_verify_chain(store2, "tenant-a")).to_be(true)

step("Replay the pre-restart order line against the reopened store")
val replay = order_add_line(store2, hs, t, host, envelope("rs-line", "restaurant.order.add"), "sess-1", "line-1", "MENU-STEAK", 1, "")
expect(replay.reason).to_equal("duplicate-key")

step("Finish the service after the restart — served, billed, balanced")
expect(line_mark_served(store2, hs, t, host, envelope("rs-serve", "restaurant.line.serve"), "sess-1", "line-1").reason).to_equal("accepted")
val closed = bill_close_session(store2, hs, t, host, envelope("rs-close", "restaurant.bill.close"), "sess-1")
expect(closed.detail).to_equal("3400")
expect(sale_journal_balanced(store2, "tenant-a")).to_be(true)
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
