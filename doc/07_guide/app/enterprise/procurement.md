# Enterprise Procurement — purchase-to-stock vertical (std.enterprise_procurement)

The purchase-to-stock proving vertical of the Simple Enterprise Suite
(design §6.4, lane `.spipe/simple_enterprise_suite` W6-B). Builds only on
`std.enterprise_store` (durable UoW / idempotency / outbox / audit) and
`std.enterprise_sale.foundation` (contexts, envelope, guarded sequence).

Module: `src/lib/nogc_sync_mut/enterprise_procurement/procurement.spl`
(`use std.enterprise_procurement` resolves via the async-tier wrapper,
mirroring `std.enterprise_sale`).

Flow:

    supplier -> requisition -> approve -> purchase order -> receipt(s)
             -> purchase invoice -> reconciliation

## One stock truth, two verticals

This is the load-bearing property of the vertical. A receipt does **not**
write a procurement-owned stock table — it inserts a signed delta into the
SAME `stock_moves` ledger the goods-sale vertical sells from, with reason
`po-receive` and `order_id` set to the PO id. Consequences:

- `sale_available_stock` sees received goods immediately;
- `sale_place_order` for a received SKU succeeds with no hand-off step —
  proven directly in the system spec;
- received-per-PO is *derived* by summing those rows
  (`proc_po_received`), never stored, so the two views cannot drift.

Each receipt also posts a balanced pair through the shared `journal`:
debit `inventory_asset` / credit `accounts_payable`, each for
`qty x unit_cost_cents`. `sale_journal_balanced` therefore stays true
across both verticals, and `proc_payable_total` is an absolute oracle
(5 units at 1000c = 5000c).

## Commands (frozen guarded sequence)

Every command runs: session -> rbac -> validation -> idempotency ->
effects in one unit of work.

| Command | Role action | Notes |
|---------|-------------|-------|
| `proc_supplier_add` | `proc.supplier.admin` (admin only) | supplier master |
| `proc_requisition_create` | `proc.requisition.create` | event `created` |
| `proc_requisition_approve` | `proc.requisition.approve` | `created` -> `approved` |
| `proc_po_create` | `proc.po.create` | requires an APPROVED requisition + known supplier; captures unit cost in cents |
| `proc_receive` | `proc.po.receive` | partial receipts allowed; writes shared `stock_moves` + journal pair |
| `proc_invoice_record` | `proc.invoice.record` | qty must not exceed received-minus-invoiced |

Role `procurement` in `role_allows` grants exactly the five non-admin
actions above; supplier registration stays admin-only.

## Denials (closed reason set only — no new reasons)

| Reason | When |
|--------|------|
| `invalid-session` | inactive, actor-mismatched, or cross-tenant session |
| `forbidden` | role lacks the action (e.g. `sales` cannot receive) |
| `not-found` | unknown supplier, requisition, or PO (incl. cross-tenant) |
| `invalid-transition` | PO from an unapproved requisition; approving twice with a fresh key |
| `insufficient-stock` | over-receipt; detail `over-receipt:<po>:remaining=<n>:got=<n>` |
| `invalid-record` | empty ids, non-positive qty/cost; invoice beyond received (detail `invoice-over-received:...`) |
| `duplicate-key` | idempotent replay; `ok=true`, detail = recorded result |

## Replay and state-dependent validation

Two checks — over-receipt and invoice-over-received — read state that the
command itself modifies on its first execution. Re-evaluating them for a
replay would deny a command that was already accepted. The rungs keep the
frozen order; those two feasibility checks are simply asked only of a
command not already recorded (`idempotency_seen`). Identity checks
(`not-found`) are state-independent and stay unconditional.

This is a general property of the frozen pattern, not a procurement quirk:
any command whose validation reads its own effect needs the same
treatment. Discovered by the W6-B green run, where the receipt-replay and
restart-replay examples failed until the two checks were made
replay-aware.

## Storage model (insert-only + derive)

| Table | Content |
|-------|---------|
| `proc_suppliers` | supplier master rows |
| `proc_req_events` | requisition event stream; status derived (`""` -> `created` -> `approved`) |
| `proc_po_rows` | one row per PO: req, supplier, sku, qty, unit cost |
| `stock_moves` (SHARED) | receipts, reason `po-receive` — there is no procurement stock table |
| `proc_invoices` | purchase-invoice rows against received qty |

Nothing is updated in place, all filtering is pure Simple over
`store_rows`, and the module holds no global mutable state.

`proc_reconcile(store, tenant_id)` returns a machine-readable line:
`open_pos=<n>;under_invoiced=<n>;fully_invoiced=<n>;payable_cents=<n>`.

## Out of scope

RFQ, quotations, and landed cost are FUTURE scope per design §6.4 and are
deliberately not modeled.

## Evidence

- Spec: `test/03_system/app/enterprise/procurement_vertical_spec.spl`
  (8/8; includes the sale-after-receipt integration case).
- Generated doc: `doc/06_spec/03_system/app/enterprise/procurement_vertical_spec.md`.
- Cross-OS: `src/app/enterprise/procurement_probe_main.spl`, gated by
  `sh scripts/check/check-enterprise-cross-os.shs`.
