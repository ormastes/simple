# Procurement Vertical — purchase-to-stock over the shared enterprise store

> The purchase-to-stock flow of the Simple Enterprise Suite (design §6.4), end to end against the durable enterprise store: an admin registers a supplier; a procurement clerk raises a requisition, has it approved, and converts it into a purchase order at a captured unit cost; goods arrive in partial receipts against the open PO; a purchase invoice is recorded against received quantity; and reconciliation reports open POs and the payable total.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Procurement Vertical — purchase-to-stock over the shared enterprise store

The purchase-to-stock flow of the Simple Enterprise Suite (design §6.4), end to end against the durable enterprise store: an admin registers a supplier; a procurement clerk raises a requisition, has it approved, and converts it into a purchase order at a captured unit cost; goods arrive in partial receipts against the open PO; a purchase invoice is recorded against received quantity; and reconciliation reports open POs and the payable total.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md (W6-B) |
| Design | doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §6.4 |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/03_system/app/enterprise/procurement_vertical_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The purchase-to-stock flow of the Simple Enterprise Suite (design §6.4),
end to end against the durable enterprise store: an admin registers a
supplier; a procurement clerk raises a requisition, has it approved, and
converts it into a purchase order at a captured unit cost; goods arrive in
partial receipts against the open PO; a purchase invoice is recorded
against received quantity; and reconciliation reports open POs and the
payable total.

The centerpiece integration: a receipt increases the SAME `stock_moves`
ledger the goods-sale vertical sells from — after a PO receipt, a sale
order for the received SKU succeeds via `sale_place_order`. One stock
truth, two verticals.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | inactive session rejected |
| rbac | forbidden | sales role cannot receive stock |
| validation | not-found / invalid-transition | unknown requisition; PO from unapproved requisition |
| validation | insufficient-stock | over-receipt beyond ordered − received |
| validation | invalid-record | invoice for more than received |
| idempotency | duplicate-key | replay returns recorded result, one effect |

## Ledger invariants

- every receipt posts a debit `inventory_asset` / credit `accounts_payable`
  pair for qty × unit cost; total debits equal total credits;
- the payable total is an absolute oracle: 5 units at 1000c = 5000c;
- received quantity per PO derives from the shared stock_moves rows
  (reason `po-receive`), never from a second stock table.

## Troubleshooting

- `insufficient-stock` with detail `over-receipt:...` is the over-receipt
  denial, not a sale-side oversell — read the detail.
- A sale failing after receipt means the receipt did not land in
  `stock_moves` — the shared-ledger contract is broken.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md (W6-B)
**Design:** doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §6.4
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W6-B).

## Scenarios

### procurement vertical — purchase-to-stock end to end

#### moves a requisition through PO, partial receipts, invoice, and a live sale

- Open a clean shared store; admin registers the supplier
   - Expected: proc_supplier_add(store, sa, t, admin, "sup-1", "Acme Supply").reason equals `accepted`
- Buyer raises a requisition for 5 units of SKU-1
   - Expected: req.reason equals `accepted`
   - Expected: proc_requisition_status(store, "tenant-a", "req-1") equals `created`
- Admin approves the requisition
   - Expected: proc_requisition_approve(store, sa, t, admin, envelope("e2e-app", "proc.requisition.approve"), "req-1").reason equals `accepted`
   - Expected: proc_requisition_status(store, "tenant-a", "req-1") equals `approved`
- Buyer converts it into a PO at 1000c unit cost
   - Expected: proc_po_create(store, sb, t, buyer, envelope("e2e-po", "proc.po.create"), "po-1", "req-1", "sup-1", usd(1000)).reason equals `accepted`
- Partial receipt: 3 of 5 arrive — shared stock ledger rises to 3
   - Expected: proc_receive(store, sb, t, buyer, envelope("e2e-rc1", "proc.po.receive"), "po-1", 3).reason equals `accepted`
   - Expected: proc_po_received(store, "tenant-a", "po-1") equals `3`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `3`
- Final receipt: remaining 2 arrive — ledger shows 5
   - Expected: proc_receive(store, sb, t, buyer, envelope("e2e-rc2", "proc.po.receive"), "po-1", 2).reason equals `accepted`
   - Expected: proc_po_received(store, "tenant-a", "po-1") equals `5`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `5`
- Journal oracle: payable is exactly 5000c and the journal balances
   - Expected: proc_payable_total(store, "tenant-a") equals `5000`
- SHARED STOCK TRUTH: a sale of the received SKU succeeds via sale_place_order
   - Expected: sold.reason equals `accepted`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `3`
- Record the purchase invoice for the 5 received units
   - Expected: proc_invoice_record(store, sb, t, buyer, envelope("e2e-inv", "proc.invoice.record"), "po-1", "inv-1", 5).reason equals `accepted`
   - Expected: proc_po_invoiced(store, "tenant-a", "po-1") equals `5`
- Reconciliation reports the closed, fully invoiced PO and the payable
   - Expected: proc_reconcile(store, "tenant-a") equals `open_pos=0;under_invoiced=0;fully_invoiced=1;payable_cents=5000`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a clean shared store; admin registers the supplier")
val store = fresh_store("e2e")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
expect(proc_supplier_add(store, sa, t, admin, "sup-1", "Acme Supply").reason).to_equal("accepted")

step("Buyer raises a requisition for 5 units of SKU-1")
val buyer = buyer_a()
val sb = session_for(buyer, t)
val req = proc_requisition_create(store, sb, t, buyer, envelope("e2e-req", "proc.requisition.create"), "req-1", "SKU-1", 5)
expect(req.reason).to_equal("accepted")
expect(proc_requisition_status(store, "tenant-a", "req-1")).to_equal("created")

step("Admin approves the requisition")
expect(proc_requisition_approve(store, sa, t, admin, envelope("e2e-app", "proc.requisition.approve"), "req-1").reason).to_equal("accepted")
expect(proc_requisition_status(store, "tenant-a", "req-1")).to_equal("approved")

step("Buyer converts it into a PO at 1000c unit cost")
expect(proc_po_create(store, sb, t, buyer, envelope("e2e-po", "proc.po.create"), "po-1", "req-1", "sup-1", usd(1000)).reason).to_equal("accepted")

step("Partial receipt: 3 of 5 arrive — shared stock ledger rises to 3")
expect(proc_receive(store, sb, t, buyer, envelope("e2e-rc1", "proc.po.receive"), "po-1", 3).reason).to_equal("accepted")
expect(proc_po_received(store, "tenant-a", "po-1")).to_equal(3)
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(3)

step("Final receipt: remaining 2 arrive — ledger shows 5")
expect(proc_receive(store, sb, t, buyer, envelope("e2e-rc2", "proc.po.receive"), "po-1", 2).reason).to_equal("accepted")
expect(proc_po_received(store, "tenant-a", "po-1")).to_equal(5)
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(5)

step("Journal oracle: payable is exactly 5000c and the journal balances")
expect(proc_payable_total(store, "tenant-a")).to_equal(5000)
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("SHARED STOCK TRUTH: a sale of the received SKU succeeds via sale_place_order")
sale_add_product(store, sa, t, admin, "SKU-1", "Widget", usd(2500))
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val cs = session_for(clerk, t)
val sold = sale_place_order(store, cs, t, clerk, envelope("e2e-sale", "sale.order.place"), "order-1", "SKU-1", 2)
expect(sold.ok).to_be(true)
expect(sold.reason).to_equal("accepted")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(3)
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)

step("Record the purchase invoice for the 5 received units")
expect(proc_invoice_record(store, sb, t, buyer, envelope("e2e-inv", "proc.invoice.record"), "po-1", "inv-1", 5).reason).to_equal("accepted")
expect(proc_po_invoiced(store, "tenant-a", "po-1")).to_equal(5)

step("Reconciliation reports the closed, fully invoiced PO and the payable")
expect(proc_reconcile(store, "tenant-a")).to_equal("open_pos=0;under_invoiced=0;fully_invoiced=1;payable_cents=5000")

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### procurement vertical — guarded denials

#### denies an over-receipt beyond ordered minus received

- Receive 4 of the 5 ordered
   - Expected: proc_receive(store, sb, t, buyer, envelope("or-rc1", "proc.po.receive"), "po-1", 4).reason equals `accepted`
- Attempt to receive 2 more — only 1 remains, must be denied with no effect
   - Expected: r.reason equals `insufficient-stock`
   - Expected: r.detail equals `over-receipt:po-1:remaining=1:got=2`
   - Expected: proc_po_received(store, "tenant-a", "po-1") equals `4`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `4`
   - Expected: proc_payable_total(store, "tenant-a") equals `4000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = seed_open_po("over_receipt")
val t = tenant_a()
val buyer = buyer_a()
val sb = session_for(buyer, t)
step("Receive 4 of the 5 ordered")
expect(proc_receive(store, sb, t, buyer, envelope("or-rc1", "proc.po.receive"), "po-1", 4).reason).to_equal("accepted")
step("Attempt to receive 2 more — only 1 remains, must be denied with no effect")
val r = proc_receive(store, sb, t, buyer, envelope("or-rc2", "proc.po.receive"), "po-1", 2)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("insufficient-stock")
expect(r.detail).to_equal("over-receipt:po-1:remaining=1:got=2")
expect(proc_po_received(store, "tenant-a", "po-1")).to_equal(4)
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(4)
expect(proc_payable_total(store, "tenant-a")).to_equal(4000)
store_close(store)
```

</details>

#### denies an invoice for more than has been received

- Invoice 4 units when only 3 were received
   - Expected: r.reason equals `invalid-record`
   - Expected: proc_po_invoiced(store, "tenant-a", "po-1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = seed_open_po("over_invoice")
val t = tenant_a()
val buyer = buyer_a()
val sb = session_for(buyer, t)
proc_receive(store, sb, t, buyer, envelope("oi-rc", "proc.po.receive"), "po-1", 3)
step("Invoice 4 units when only 3 were received")
val r = proc_invoice_record(store, sb, t, buyer, envelope("oi-inv", "proc.invoice.record"), "po-1", "inv-1", 4)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")
expect(proc_po_invoiced(store, "tenant-a", "po-1")).to_equal(0)
store_close(store)
```

</details>

#### denies a PO from an unapproved requisition and approval of a missing one

- PO from a merely created requisition is an invalid transition
   - Expected: r.reason equals `invalid-transition`
- Approving a nonexistent requisition is not-found
   - Expected: proc_requisition_approve(store, sa, t, admin, envelope("ua-app", "proc.requisition.approve"), "req-404").reason equals `not-found`
- Approving twice with a fresh key is an invalid transition
   - Expected: proc_requisition_approve(store, sa, t, admin, envelope("ua-app2", "proc.requisition.approve"), "req-1").reason equals `invalid-transition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("unapproved")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
proc_supplier_add(store, sa, t, admin, "sup-1", "Acme Supply")
val buyer = buyer_a()
val sb = session_for(buyer, t)
proc_requisition_create(store, sb, t, buyer, envelope("ua-req", "proc.requisition.create"), "req-1", "SKU-1", 5)
step("PO from a merely created requisition is an invalid transition")
val r = proc_po_create(store, sb, t, buyer, envelope("ua-po", "proc.po.create"), "po-1", "req-1", "sup-1", usd(1000))
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-transition")
step("Approving a nonexistent requisition is not-found")
expect(proc_requisition_approve(store, sa, t, admin, envelope("ua-app", "proc.requisition.approve"), "req-404").reason).to_equal("not-found")
step("Approving twice with a fresh key is an invalid transition")
proc_requisition_approve(store, sa, t, admin, envelope("ua-app1", "proc.requisition.approve"), "req-1")
expect(proc_requisition_approve(store, sa, t, admin, envelope("ua-app2", "proc.requisition.approve"), "req-1").reason).to_equal("invalid-transition")
store_close(store)
```

</details>

#### denies bad sessions and wrong roles

- Inactive session rejected
   - Expected: proc_receive(store, dead, t, buyer, envelope("g-rc", "proc.po.receive"), "po-1", 1).reason equals `invalid-session`
- Sales role cannot receive against a PO
   - Expected: proc_receive(store, session_for(clerk, t), t, clerk, envelope("g-rc2", "proc.po.receive"), "po-1", 1).reason equals `forbidden`
- Procurement role cannot add suppliers (admin-only)
   - Expected: proc_supplier_add(store, session_for(buyer, t), t, buyer, "sup-2", "Bmart").reason equals `forbidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = seed_open_po("guards")
val t = tenant_a()
val buyer = buyer_a()
var dead = session_for(buyer, t)
dead.active = false
step("Inactive session rejected")
expect(proc_receive(store, dead, t, buyer, envelope("g-rc", "proc.po.receive"), "po-1", 1).reason).to_equal("invalid-session")
step("Sales role cannot receive against a PO")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
expect(proc_receive(store, session_for(clerk, t), t, clerk, envelope("g-rc2", "proc.po.receive"), "po-1", 1).reason).to_equal("forbidden")
step("Procurement role cannot add suppliers (admin-only)")
expect(proc_supplier_add(store, session_for(buyer, t), t, buyer, "sup-2", "Bmart").reason).to_equal("forbidden")
store_close(store)
```

</details>

### procurement vertical — idempotent replay produces exactly one effect

#### replaying the same receipt command changes nothing

- Receive once
   - Expected: proc_receive(store, sb, t, buyer, envelope("same-key", "proc.po.receive"), "po-1", 3).reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `po-1`
- No second effect — stock, outbox, and payable unchanged
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `stock_after`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after`
   - Expected: proc_payable_total(store, "tenant-a") equals `payable_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = seed_open_po("replay")
val t = tenant_a()
val buyer = buyer_a()
val sb = session_for(buyer, t)
step("Receive once")
expect(proc_receive(store, sb, t, buyer, envelope("same-key", "proc.po.receive"), "po-1", 3).reason).to_equal("accepted")
val stock_after = sale_available_stock(store, "tenant-a", "SKU-1")
val outbox_after = outbox_pending(store, "tenant-a").len()
val payable_after = proc_payable_total(store, "tenant-a")
step("Replay the SAME idempotency key")
val replay = proc_receive(store, sb, t, buyer, envelope("same-key", "proc.po.receive"), "po-1", 3)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("po-1")
step("No second effect — stock, outbox, and payable unchanged")
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(stock_after)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after)
expect(proc_payable_total(store, "tenant-a")).to_equal(payable_after)
store_close(store)
```

</details>

### procurement vertical — tenant isolation

#### tenant B sees none of tenant A's procurement state

- Tenant B sees no requisition, no receipts, no payable
   - Expected: proc_requisition_status(store, "tenant-b", "req-1") equals ``
   - Expected: proc_payable_total(store, "tenant-b") equals `0`
- A tenant-B buyer cannot receive against tenant A's PO
   - Expected: proc_receive(store, sbb, tb, buyer_b, envelope("iso-rc", "proc.po.receive"), "po-1", 1).reason equals `not-found`
- A cross-tenant session is rejected outright
   - Expected: proc_receive(store, sbb, ta, buyer_b, envelope("iso-rc2", "proc.po.receive"), "po-1", 1).reason equals `invalid-session`
- Tenant A's ledger is untouched
   - Expected: proc_po_received(store, "tenant-a", "po-1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = seed_open_po("isolation")
step("Tenant B sees no requisition, no receipts, no payable")
expect(proc_requisition_status(store, "tenant-b", "req-1")).to_equal("")
expect(proc_payable_total(store, "tenant-b")).to_equal(0)
step("A tenant-B buyer cannot receive against tenant A's PO")
val tb = tenant_b()
val buyer_b = ActorContext(actor_id: "buyer-b", role: "procurement")
val sbb = session_for(buyer_b, tb)
expect(proc_receive(store, sbb, tb, buyer_b, envelope("iso-rc", "proc.po.receive"), "po-1", 1).reason).to_equal("not-found")
step("A cross-tenant session is rejected outright")
val ta = tenant_a()
expect(proc_receive(store, sbb, ta, buyer_b, envelope("iso-rc2", "proc.po.receive"), "po-1", 1).reason).to_equal("invalid-session")
step("Tenant A's ledger is untouched")
expect(proc_po_received(store, "tenant-a", "po-1")).to_equal(0)
store_close(store)
```

</details>

### procurement vertical — state survives restart

#### reopens the database with PO, receipts, payable, and replay guard intact

- Close the store (simulated shutdown)
- Reopen and verify PO state, shared stock, payable, and audit
   - Expected: proc_requisition_status(store2, "tenant-a", "req-1") equals `approved`
   - Expected: proc_po_received(store2, "tenant-a", "po-1") equals `3`
   - Expected: sale_available_stock(store2, "tenant-a", "SKU-1") equals `3`
   - Expected: proc_payable_total(store2, "tenant-a") equals `3000`
- Replay the pre-restart receipt against the reopened store
   - Expected: proc_receive(store2, sb, t, buyer, envelope("restart-key", "proc.po.receive"), "po-1", 3).reason equals `duplicate-key`
   - Expected: proc_po_received(store2, "tenant-a", "po-1") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = seed_open_po("restart")
val t = tenant_a()
val buyer = buyer_a()
val sb = session_for(buyer, t)
proc_receive(store, sb, t, buyer, envelope("restart-key", "proc.po.receive"), "po-1", 3)
step("Close the store (simulated shutdown)")
store_close(store)
step("Reopen and verify PO state, shared stock, payable, and audit")
val store2 = store_open(db_path("restart"))
expect(store2.open_ok).to_be(true)
expect(proc_requisition_status(store2, "tenant-a", "req-1")).to_equal("approved")
expect(proc_po_received(store2, "tenant-a", "po-1")).to_equal(3)
expect(sale_available_stock(store2, "tenant-a", "SKU-1")).to_equal(3)
expect(proc_payable_total(store2, "tenant-a")).to_equal(3000)
expect(sale_journal_balanced(store2, "tenant-a")).to_be(true)
expect(audit_verify_chain(store2, "tenant-a")).to_be(true)
step("Replay the pre-restart receipt against the reopened store")
expect(proc_receive(store2, sb, t, buyer, envelope("restart-key", "proc.po.receive"), "po-1", 3).reason).to_equal("duplicate-key")
expect(proc_po_received(store2, "tenant-a", "po-1")).to_equal(3)
store_close(store2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `.spipe/simple_enterprise_suite/state.md (W6-B)`
- **Design:** `doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §6.4`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
