# Finance Vertical — trial balance, AR/AP, period close and lock

> Finance reporting and period control over the SAME journal the goods-sale vertical posts (lane `.spipe/simple_enterprise_suite`, W6-C; design §6.3). A seeded sale + payment flow is checked against ABSOLUTE hand-computed oracle totals (never derived from the module under test); accounts receivable opens with the unpaid order and clears on payment; an admin-guarded period close writes an insert-only lock row capturing the trial-balance snapshot; and — the money case — a goods_sale REFUND dated inside the closed period is denied THROUGH the shared posting seam (`enterprise_store.records.journal_post_pair`), proving existing modules inherit the period check without knowing finance exists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Finance Vertical — trial balance, AR/AP, period close and lock

Finance reporting and period control over the SAME journal the goods-sale vertical posts (lane `.spipe/simple_enterprise_suite`, W6-C; design §6.3). A seeded sale + payment flow is checked against ABSOLUTE hand-computed oracle totals (never derived from the module under test); accounts receivable opens with the unpaid order and clears on payment; an admin-guarded period close writes an insert-only lock row capturing the trial-balance snapshot; and — the money case — a goods_sale REFUND dated inside the closed period is denied THROUGH the shared posting seam (`enterprise_store.records.journal_post_pair`), proving existing modules inherit the period check without knowing finance exists.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/03_system/app/enterprise/finance_vertical_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Finance reporting and period control over the SAME journal the goods-sale
vertical posts (lane `.spipe/simple_enterprise_suite`, W6-C; design §6.3).
A seeded sale + payment flow is checked against ABSOLUTE hand-computed
oracle totals (never derived from the module under test); accounts
receivable opens with the unpaid order and clears on payment; an
admin-guarded period close writes an insert-only lock row capturing the
trial-balance snapshot; and — the money case — a goods_sale REFUND dated
inside the closed period is denied THROUGH the shared posting seam
(`enterprise_store.records.journal_post_pair`), proving existing modules
inherit the period check without knowing finance exists.

## Hand-computed oracle (price 2500c, qty 2)

| Step | Debit | Credit |
|------|-------|--------|
| place | accounts_receivable 5000 | sales_revenue 5000 |
| pay | cash 5000 | accounts_receivable 5000 |
| totals | 10000 | 10000 |

## Known limitation (documented here on purpose)

Only postings routed through `records.journal_post_pair` are period-checked.
goods_sale and restaurant are wired through the seam; a module inserting
into `journal` with raw `store_insert_row` bypasses the lock. New journal
writers MUST use the seam (guide: doc/07_guide/app/enterprise/finance.md).

## Troubleshooting

- `invalid-transition` on a NEW sale after close: the close's
  `period_end_epoch` is in the future, so ALL current-dated postings are
  locked — that is the hard-freeze semantic, not a bug.
- Empty `fin_ap_open`: nothing has credited `accounts_payable` for the
  tenant, or every credit has been matched by a settling debit. The report
  reads the SHARED journal, not a `payables` table — there is no such table
  and no second copy of payable state (that is the point).

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W6-C, finance vertical).

## Scenarios

### finance vertical — trial balance against an absolute oracle

#### matches hand-computed per-account totals and balances

- Seed a sale (2500c x 2) placed and paid
- Trial balance totals are the hand-computed 10000/10000
   - Expected: tb.debit_total equals `10000`
   - Expected: tb.credit_total equals `10000`
- Per-account lines match the oracle table
   - Expected: ar.0 equals `5000`
   - Expected: ar.1 equals `5000`
   - Expected: cash.0 equals `5000`
   - Expected: cash.1 equals `0`
   - Expected: rev.0 equals `0`
   - Expected: rev.1 equals `5000`
- Raw journal row count is exactly 4 (two balanced pairs)
   - Expected: journal_rows(store, "tenant-a") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed a sale (2500c x 2) placed and paid")
val store = fresh_store("tb")
seed_sale(store, tenant_a())

step("Trial balance totals are the hand-computed 10000/10000")
val tb = fin_trial_balance(store, "tenant-a")
expect(tb.debit_total).to_equal(10000)
expect(tb.credit_total).to_equal(10000)
expect(tb.balanced).to_be(true)

step("Per-account lines match the oracle table")
val ar = fin_trial_balance_account(tb, "accounts_receivable")
expect(ar.0).to_equal(5000)
expect(ar.1).to_equal(5000)
val cash = fin_trial_balance_account(tb, "cash")
expect(cash.0).to_equal(5000)
expect(cash.1).to_equal(0)
val rev = fin_trial_balance_account(tb, "sales_revenue")
expect(rev.0).to_equal(0)
expect(rev.1).to_equal(5000)

step("Raw journal row count is exactly 4 (two balanced pairs)")
expect(journal_rows(store, "tenant-a")).to_equal(4)
store_close(store)
```

</details>

### finance vertical — accounts receivable and payable

#### shows the unpaid order in AR and clears it after payment

- Place an order without paying
- AR lists the unpaid order with the 5000c open amount
   - Expected: open_before.len() equals `1`
   - Expected: open_before[0].0 equals `order-200`
   - Expected: open_before[0].1 equals `5000`
- Payment clears the receivable
   - Expected: fin_ar_open(store, "tenant-a").len() equals `0`
- AP is empty because nothing ever credited accounts_payable
   - Expected: fin_ap_open(store, "tenant-a").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Place an order without paying")
val store = fresh_store("ar")
val t = tenant_a()
val admin = admin_a()
val admin_session = session_for(admin, t)
sale_add_product(store, admin_session, t, admin, "SKU-1", "Widget", usd(2500))
sale_receive_stock(store, admin_session, t, admin, "SKU-1", 10)
val clerk = clerk_a()
val clerk_session = session_for(clerk, t)
sale_place_order(store, clerk_session, t, clerk, envelope("ar-ord-1", "sale.order.place"), "order-200", "SKU-1", 2)

step("AR lists the unpaid order with the 5000c open amount")
val open_before = fin_ar_open(store, "tenant-a")
expect(open_before.len()).to_equal(1)
expect(open_before[0].0).to_equal("order-200")
expect(open_before[0].1).to_equal(5000)

step("Payment clears the receivable")
sale_pay_order(store, clerk_session, t, clerk, envelope("ar-pay-1", "sale.order.pay"), "order-200")
expect(fin_ar_open(store, "tenant-a").len()).to_equal(0)

step("AP is empty because nothing ever credited accounts_payable")
expect(fin_ap_open(store, "tenant-a").len()).to_equal(0)
store_close(store)
```

</details>

### finance vertical — AP reads the shared journal's payable postings

#### lists a real procurement payable with the hand-computed total

- Seed two purchase-to-stock flows (oracle 3x700 + 2x250 = 2600c)
- The journal really holds the payable (independent oracle side)
   - Expected: proc_payable_total(store, "tenant-a") equals `2600`
   - Expected: fin_trial_balance_account(tb, "accounts_payable").1 equals `2600`
- fin_ap_open returns one line per PO summing to the same 2600c
   - Expected: ap.len() equals `2`
   - Expected: ap_total equals `2600`
   - Expected: ap[0].0 equals `po-1`
   - Expected: ap[0].1 equals `2100`
   - Expected: ap[1].0 equals `po-2`
   - Expected: ap[1].1 equals `500`
- Settling a payable through the shared seam removes it from AP
   - Expected: ap_after.len() equals `1`
   - Expected: ap_after[0].0 equals `po-1`
   - Expected: ap_after[0].1 equals `2100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed two purchase-to-stock flows (oracle 3x700 + 2x250 = 2600c)")
val store = fresh_store("ap")
proc_setup(store)
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
seed_payable(store, t, "SUP-1", "REQ-1", "po-1", "SKU-9", 3, 700, 3)
seed_payable(store, t, "SUP-1", "REQ-2", "po-2", "SKU-8", 4, 250, 2)

step("The journal really holds the payable (independent oracle side)")
expect(proc_payable_total(store, "tenant-a")).to_equal(2600)
val tb = fin_trial_balance(store, "tenant-a")
expect(fin_trial_balance_account(tb, "accounts_payable").1).to_equal(2600)

step("fin_ap_open returns one line per PO summing to the same 2600c")
val ap = fin_ap_open(store, "tenant-a")
expect(ap.len()).to_equal(2)
var ap_total: i64 = 0
for entry in ap:
    ap_total = ap_total + entry.1
expect(ap_total).to_equal(2600)
expect(ap[0].0).to_equal("po-1")
expect(ap[0].1).to_equal(2100)
expect(ap[1].0).to_equal("po-2")
expect(ap[1].1).to_equal(500)

step("Settling a payable through the shared seam removes it from AP")
val fin = fin_clerk()
val fin_session = session_for(fin, t)
val paid = fin_post_journal_guarded(store, fin_session, t, fin, envelope("ap-settle-1", "finance.journal.post"), "po-2", "accounts_payable", "cash", 500, 1755000000)
expect(paid.ok).to_be(true)
val ap_after = fin_ap_open(store, "tenant-a")
expect(ap_after.len()).to_equal(1)
expect(ap_after[0].0).to_equal("po-1")
expect(ap_after[0].1).to_equal(2100)
store_close(store)
```

</details>

#### keeps one tenant's payables out of another's AP report

- Only tenant A has procurement activity
   - Expected: fin_ap_open(store, "tenant-a").len() equals `1`
   - Expected: fin_ap_open(store, "tenant-b").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Only tenant A has procurement activity")
val store = fresh_store("ap_tenants")
proc_setup(store)
seed_payable(store, tenant_a(), "SUP-1", "REQ-1", "po-1", "SKU-9", 3, 700, 3)
expect(fin_ap_open(store, "tenant-a").len()).to_equal(1)
expect(fin_ap_open(store, "tenant-b").len()).to_equal(0)
store_close(store)
```

</details>

### finance vertical — period close locks the ledger through the shared seam

#### denies a backdated goods_sale refund after close (the money case)

- Seed a paid sale, verify refund would otherwise be legal
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `paid`
   - Expected: fin_period_status(store, "tenant-a") equals `0`
- Admin closes the period through a far-future end (hard freeze)
   - Expected: closed.reason equals `accepted`
   - Expected: fin_period_status(store, "tenant-a") equals `far_future()`
- A goods_sale refund now lands inside the closed period — denied via the seam
   - Expected: refund.reason equals `invalid-transition`
- The denied refund left no journal rows and no status change
   - Expected: journal_rows(store, "tenant-a") equals `rows_before`
   - Expected: sale_order_status(store, "tenant-a", "order-100") equals `paid`
- A backdated guarded finance posting is denied the same way
   - Expected: post.reason equals `invalid-transition`
   - Expected: journal_rows(store, "tenant-a") equals `rows_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed a paid sale, verify refund would otherwise be legal")
val store = fresh_store("close")
val t = tenant_a()
seed_sale(store, t)
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("paid")
expect(fin_period_status(store, "tenant-a")).to_equal(0)

step("Admin closes the period through a far-future end (hard freeze)")
val admin = admin_a()
val admin_session = session_for(admin, t)
val closed = fin_period_close(store, admin_session, t, admin, envelope("close-1", "finance.period.close"), far_future(), 1755000000)
expect(closed.reason).to_equal("accepted")
expect(closed.ok).to_be(true)
expect(fin_period_status(store, "tenant-a")).to_equal(far_future())

step("A goods_sale refund now lands inside the closed period — denied via the seam")
val clerk = clerk_a()
val clerk_session = session_for(clerk, t)
val rows_before = journal_rows(store, "tenant-a")
val refund = sale_refund_order(store, clerk_session, t, clerk, envelope("close-ref-1", "sale.order.refund"), "order-100")
expect(refund.ok).to_be(false)
expect(refund.reason).to_equal("invalid-transition")

step("The denied refund left no journal rows and no status change")
expect(journal_rows(store, "tenant-a")).to_equal(rows_before)
expect(sale_order_status(store, "tenant-a", "order-100")).to_equal("paid")

step("A backdated guarded finance posting is denied the same way")
val fin = fin_clerk()
val fin_session = session_for(fin, t)
val post = fin_post_journal_guarded(store, fin_session, t, fin, envelope("close-post-1", "finance.journal.post"), "adj-1", "cash", "sales_revenue", 100, 1700000000)
expect(post.ok).to_be(false)
expect(post.reason).to_equal("invalid-transition")
expect(journal_rows(store, "tenant-a")).to_equal(rows_before)
store_close(store)
```

</details>

#### captures the close snapshot and replays idempotently

- Seed and close with the oracle totals on the books
   - Expected: closed.reason equals `accepted`
- The close report snapshot equals the hand-computed totals
   - Expected: snap.0 equals `10000`
   - Expected: snap.1 equals `10000`
- Replaying the SAME close returns duplicate-key with one lock row
   - Expected: replay.reason equals `duplicate-key`
   - Expected: lock_rows(store, "tenant-a") equals `1`
- An earlier or equal period end is an invalid transition
   - Expected: earlier.reason equals `invalid-transition`
- A sales clerk may not close periods
   - Expected: role_denial.reason equals `forbidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed and close with the oracle totals on the books")
val store = fresh_store("snapshot")
val t = tenant_a()
seed_sale(store, t)
val admin = admin_a()
val admin_session = session_for(admin, t)
val closed = fin_period_close(store, admin_session, t, admin, envelope("snap-close-1", "finance.period.close"), far_future(), 1755000000)
expect(closed.reason).to_equal("accepted")

step("The close report snapshot equals the hand-computed totals")
val snap = fin_close_report(store, "tenant-a")
expect(snap.0).to_equal(10000)
expect(snap.1).to_equal(10000)

step("Replaying the SAME close returns duplicate-key with one lock row")
val replay = fin_period_close(store, admin_session, t, admin, envelope("snap-close-1", "finance.period.close"), far_future(), 1755000099)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(lock_rows(store, "tenant-a")).to_equal(1)

step("An earlier or equal period end is an invalid transition")
val earlier = fin_period_close(store, admin_session, t, admin, envelope("snap-close-2", "finance.period.close"), 1700000000, 1755000100)
expect(earlier.ok).to_be(false)
expect(earlier.reason).to_equal("invalid-transition")

step("A sales clerk may not close periods")
val clerk = clerk_a()
val clerk_session = session_for(clerk, t)
val role_denial = fin_period_close(store, clerk_session, t, clerk, envelope("snap-close-3", "finance.period.close"), far_future() + 1, 1755000101)
expect(role_denial.reason).to_equal("forbidden")
store_close(store)
```

</details>

### finance vertical — tenant isolation

#### tenant A's close never locks or leaks into tenant B

- Seed and close tenant A
   - Expected: fin_period_status(store, "tenant-a") equals `far_future()`
- Tenant B's ledger is untouched and still open for posting
   - Expected: fin_period_status(store, "tenant-b") equals `0`
   - Expected: fin_trial_balance(store, "tenant-b").debit_total equals `0`
   - Expected: fin_trial_balance(store, "tenant-b").debit_total equals `10000`
- Tenant A's totals are unchanged by B's activity
   - Expected: fin_trial_balance(store, "tenant-a").debit_total equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed and close tenant A")
val store = fresh_store("tenants")
val ta = tenant_a()
seed_sale(store, ta)
val admin = admin_a()
val a_session = session_for(admin, ta)
fin_period_close(store, a_session, ta, admin, envelope("iso-close-1", "finance.period.close"), far_future(), 1755000000)
expect(fin_period_status(store, "tenant-a")).to_equal(far_future())

step("Tenant B's ledger is untouched and still open for posting")
val tb_t = tenant_b()
expect(fin_period_status(store, "tenant-b")).to_equal(0)
expect(fin_trial_balance(store, "tenant-b").debit_total).to_equal(0)
seed_sale(store, tb_t)
expect(fin_trial_balance(store, "tenant-b").debit_total).to_equal(10000)
expect(fin_trial_balance(store, "tenant-b").balanced).to_be(true)

step("Tenant A's totals are unchanged by B's activity")
expect(fin_trial_balance(store, "tenant-a").debit_total).to_equal(10000)
store_close(store)
```

</details>

### finance vertical — state survives restart

#### reopens with the lock, snapshot, and lock enforcement intact

- Seed, close, and close the store handle
- Reopen the same database
- Lock and snapshot survived
   - Expected: fin_period_status(store2, "tenant-a") equals `far_future()`
   - Expected: snap.0 equals `10000`
   - Expected: snap.1 equals `10000`
- The seam still denies a refund after restart
   - Expected: refund.reason equals `invalid-transition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed, close, and close the store handle")
val store = fresh_store("restart")
val t = tenant_a()
seed_sale(store, t)
val admin = admin_a()
val admin_session = session_for(admin, t)
fin_period_close(store, admin_session, t, admin, envelope("restart-close-1", "finance.period.close"), far_future(), 1755000000)
store_close(store)

step("Reopen the same database")
val store2 = store_open(db_path("restart"))
sale_setup(store2)
fin_setup(store2)

step("Lock and snapshot survived")
expect(fin_period_status(store2, "tenant-a")).to_equal(far_future())
val snap = fin_close_report(store2, "tenant-a")
expect(snap.0).to_equal(10000)
expect(snap.1).to_equal(10000)

step("The seam still denies a refund after restart")
val clerk = clerk_a()
val clerk_session = session_for(clerk, t)
val refund = sale_refund_order(store2, clerk_session, t, clerk, envelope("restart-ref-1", "sale.order.refund"), "order-100")
expect(refund.reason).to_equal("invalid-transition")
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

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
