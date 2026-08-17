# Enterprise Finance — reporting and period control

`std.nogc_sync_mut.enterprise_finance` (lane `.spipe/simple_enterprise_suite`,
W6-C) adds finance **reporting** and **period control** over the journal the
goods-sale and restaurant verticals already write. It does **not** fork the
journal: every report reads the same `journal` table `goods_sale.post_journal`
posts to.

System spec: `test/03_system/app/enterprise/finance_vertical_spec.spl`
(generated doc: `doc/06_spec/03_system/app/enterprise/finance_vertical_spec.md`).

## Surface

| Function | Kind | Meaning |
|----------|------|---------|
| `fin_setup(store)` | migration | insert-only `period_locks` table (`fin_001_period_locks`) |
| `fin_trial_balance(store, tenant)` | pure read | per-account debit/credit lines + totals + `balanced` |
| `fin_trial_balance_account(tb, account)` | pure read | one account's `(debit, credit)` |
| `fin_ar_open(store, tenant)` | pure read | `[(order_id, open_cents)]` for placed-but-unpaid orders |
| `fin_ap_open(store, tenant)` | pure read | `[(ref_id, outstanding_cents)]` derived from the journal's `accounts_payable` account |
| `fin_period_status(store, tenant)` | pure read | latest closed `period_end_epoch` (0 = none) |
| `fin_close_report(store, tenant)` | pure read | `(debit_total, credit_total)` snapshot captured in the latest close row |
| `fin_period_close(...)` | guarded command | insert-only period lock, capturing the trial balance at close |
| `fin_post_journal_guarded(...)` | guarded command | one explicitly dated debit/credit pair through the seam |

`finance_async.spl` mirrors all of the above as `async fn ..._async` with
identical semantics — no extra state, no extra effects.

Role policy: `role_allows("finance", ...)` grants `finance.period.close` and
`finance.journal.post`; `admin` retains both. Denials use only the frozen
closed reason set (`invalid-session`, `forbidden`, `invalid-record`,
`invalid-transition`, `duplicate-key`). No module-global mutable state; all
filtering is pure Simple over `store_rows`.

### `fin_ap_open` reads the journal, not a payables table

`fin_ap_open` groups the tenant's `accounts_payable` journal postings by the
posting's ref (`journal.order_id`), nets **credits minus debits**, and returns
the refs that still owe money. There is no `payables` table anywhere in the
suite, and there must not be one: the journal is authoritative and modules
read it rather than mirroring it. `enterprise_procurement.proc_receive`
already credits `accounts_payable` through the shared journal; a settlement
debits the same account through `records.journal_post_pair`. A separate
payables projection would be a second copy of state that can drift from the
ledger and would need its own period-lock story. Any future module that
credits `accounts_payable` is picked up by this report for free.

An empty result therefore means one of two real things — nothing credited
`accounts_payable`, or every credit has been settled — never "the module
isn't installed".

**Bug history (fixed 2026-08-16, lane W9-A).** This read used to gate on
`store_migration_applied(store, "proc_001_payables")`, a migration id that
NOTHING in the tree ever applies (`enterprise_procurement` applies
`proc_001_suppliers`). AP line items were therefore ALWAYS empty — in the
library and on `GET /fin/ap` — while a nonzero payable genuinely existed on
the books. A silent wrong answer in a finance report. Regression cover:
`test/03_system/app/enterprise/finance_vertical_spec.spl`, describe
*"finance vertical — AP reads the shared journal's payable postings"*, which
seeds two real purchase-to-stock flows and checks the lines against a
hand-computed 2100 + 500 = 2600c oracle plus a settlement that clears a line.

## Where the period check lives

**The shared posting seam is `enterprise_store.records`**, which now owns three
period functions:

- `period_latest_close(store, tenant)` — the tenant's newest closed
  `period_end_epoch`, or `0` when the finance migration is absent (probe, not
  crash: `period_locks_present` checks the migration ledger first).
- `journal_post_allowed(store, tenant, posted_at)` — **read-only** predicate,
  true when a posting dated `posted_at` would be accepted.
- `journal_post_pair(store, tenant, ref, debit_acct, credit_acct, cents, posted_at)`
  — the single write helper. Returns `false` and writes **no rows** when
  `posted_at <= period_latest_close(...)`.

`goods_sale.post_journal` and `restaurant.rest_post_journal` are now thin
wrappers over `journal_post_pair`, so both verticals inherit the period lock
without importing anything from finance — finance depends on the store layer,
never the reverse.

### Two-stage enforcement (and why)

Each guarded command samples `time_now()` **once**, calls
`journal_post_allowed` during domain validation — **before** `uow_begin` — and
denies `invalid-transition` there; the same timestamp is then passed into
`journal_post_pair`, which re-checks inside the unit of work.

The pre-UoW check is not redundant. On the current store backend
`uow_rollback` does **not** undo already-issued inserts: a refund denied only
inside the UoW still left its `order_events` "refunded" row behind, flipping
the derived order status. Validating before any write makes a denial write
nothing at all. The in-seam check remains as the guarantee for any future
caller that posts outside a command.

### Coverage limits — read this before adding a journal writer

- **Only postings routed through `journal_post_pair` are period-checked.** A
  module that inserts into `journal` with raw `store_insert_row` bypasses the
  lock entirely. `goods_sale` and `restaurant` are wired through the seam; any
  NEW journal writer MUST use it.
- The lock is a **hard freeze through a date**, not a per-period window: after
  closing through `period_end_epoch`, *every* posting dated at or before that
  epoch is denied, including current-dated ones when the close date is in the
  future. That is deliberate and is what the spec exercises.
- `period_locks` is insert-only; there is no reopen command. A later close
  must use a strictly greater `period_end_epoch`.
- Idempotency is evaluated **before** the period transition check in
  `fin_period_close`, so replaying an applied close returns `duplicate-key`
  rather than being misreported as `invalid-transition` against its own lock.
- Tax, multi-currency, budgets and fixed assets are out of scope.

## Cross-OS

`src/app/enterprise/finance_probe_main.spl` is the minimal SMF-safe entry;
`sh scripts/check/check-enterprise-cross-os.shs` compiles it for the host and
`x86_64-unknown-simpleos` (PASS — 6 probes checked).
