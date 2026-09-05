# Enterprise Finance Reporting — a real trial balance over the shared journal

> Evidence for `std.enterprise_finance.reporting` (lane `.spipe/simple_enterprise_suite`, W18-B). A **trial balance** folds every posted journal row for a tenant into per-account debit/credit totals and the ledger-integrity invariant **TOTAL DEBITS == TOTAL CREDITS**. Money is in integer minor units (cents); the folds are exact `i64` sums, never floats.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Finance Reporting — a real trial balance over the shared journal

Evidence for `std.enterprise_finance.reporting` (lane `.spipe/simple_enterprise_suite`, W18-B). A **trial balance** folds every posted journal row for a tenant into per-account debit/credit totals and the ledger-integrity invariant **TOTAL DEBITS == TOTAL CREDITS**. Money is in integer minor units (cents); the folds are exact `i64` sums, never floats.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Evidence for `std.enterprise_finance.reporting` (lane
`.spipe/simple_enterprise_suite`, W18-B). A **trial balance** folds every
posted journal row for a tenant into per-account debit/credit totals and the
ledger-integrity invariant **TOTAL DEBITS == TOTAL CREDITS**. Money is in
integer minor units (cents); the folds are exact `i64` sums, never floats.

Journal entries are posted through the REAL guarded path
`fin_post_journal_guarded` (session -> RBAC -> validation -> idempotency ->
`records.journal_post_pair`), which writes one balanced debit/credit pair per
call — no rows are fabricated behind the guard to manufacture a balanced
result.

## What each `it` proves

- **Per-account math + debits==credits**: two balanced postings across three
  accounts; every account's (debit, credit) is asserted against an absolute
  oracle and the report is `balanced: true` with equal totals.
- **Tenant isolation (reproduce-first)**: tenant B posts into the SAME journal
  table. The spec FIRST proves the leak source exists — the raw `journal`
  table holds tenant B's row — then proves tenant A's report excludes it and
  tenant B sees only its own. A report that read all rows would fail these.
- **Imbalance is reported, not hidden (reproduce-first)**: a single-sided row
  is inserted directly into `journal` to SIMULATE a corrupt / partially-posted
  ledger (the guarded path cannot produce this — it only writes balanced
  pairs). The report must surface `balanced: false` rather than silently
  render wrong numbers.
- **Read through the session**: an inactive session is refused with
  `ok:false, reason:"invalid-session"` and no data.
- **Period-scoped variant**: after `fin_period_close` snapshots the totals,
  `trial_balance_at_close` returns the period-boundary totals; a boundary
  before any close reports `no-close`.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite, W18-B.

## Scenarios

### finance reporting — trial balance per-account math and debits==credits

#### folds balanced postings into per-account totals with a balanced ledger

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- folds balanced postings into per-account totals with a balanced ledger
- Post a sale: debit cash / credit sales_revenue 10000 cents
- Post a purchase: debit inventory / credit cash 3000 cents
- Run the trial balance for tenant A's session
- Assert every account's debit/credit against an absolute oracle
   - Expected: cash.0 equals `10000)   # cash debited by the sale`
   - Expected: cash.1 equals `3000)    # cash credited by the purchase`
   - Expected: rev.0 equals `0`
   - Expected: rev.1 equals `10000`
   - Expected: inv.0 equals `3000`
   - Expected: inv.1 equals `0`
- Assert the fundamental invariant: total debits == total credits
   - Expected: rep.debit_total equals `13000`
   - Expected: rep.credit_total equals `13000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("folds balanced postings into per-account totals with a balanced ledger")
val store = setup_store()
step("Post a sale: debit cash / credit sales_revenue 10000 cents")
expect(post(store, "tenant-a", "k1", "inv-1", "cash", "sales_revenue", 10000)).to_be(true)
step("Post a purchase: debit inventory / credit cash 3000 cents")
expect(post(store, "tenant-a", "k2", "po-1", "inventory", "cash", 3000)).to_be(true)

step("Run the trial balance for tenant A's session")
val rep = trial_balance(store, session_for("acct-tenant-a", "tenant-a"), tenant("tenant-a"), actor("acct-tenant-a"))
expect(rep.ok).to_be(true)

step("Assert every account's debit/credit against an absolute oracle")
val cash = trial_balance_account(rep, "cash")
expect(cash.0).to_equal(10000)   # cash debited by the sale
expect(cash.1).to_equal(3000)    # cash credited by the purchase
val rev = trial_balance_account(rep, "sales_revenue")
expect(rev.0).to_equal(0)
expect(rev.1).to_equal(10000)
val inv = trial_balance_account(rep, "inventory")
expect(inv.0).to_equal(3000)
expect(inv.1).to_equal(0)

step("Assert the fundamental invariant: total debits == total credits")
expect(rep.debit_total).to_equal(13000)
expect(rep.credit_total).to_equal(13000)
expect(rep.balanced).to_be(true)
store_close(store)
```

</details>

### finance reporting — tenant isolation (reproduce-first)

#### excludes another tenant's journal rows from the report

- excludes another tenant's journal rows from the report
- Tenant A posts 10000; tenant B posts 500 into the SAME journal
- Reproduce-first: prove the leak source exists — the raw journal holds tenant B's row
   - Expected: b_rows equals `2)   # tenant B's balanced pair is really in the table`
- Tenant A's report excludes tenant B — totals are A's alone
   - Expected: repA.debit_total equals `10000`
   - Expected: repA.credit_total equals `10000`
   - Expected: trial_balance_account(repA, "cash").0 equals `10000`
- Tenant B's report sees only its own 500
   - Expected: repB.debit_total equals `500`
   - Expected: repB.credit_total equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("excludes another tenant's journal rows from the report")
val store = setup_store()
step("Tenant A posts 10000; tenant B posts 500 into the SAME journal")
expect(post(store, "tenant-a", "a1", "inv-a", "cash", "sales_revenue", 10000)).to_be(true)
expect(post(store, "tenant-b", "b1", "inv-b", "cash", "sales_revenue", 500)).to_be(true)

step("Reproduce-first: prove the leak source exists — the raw journal holds tenant B's row")
var b_rows = 0
for row in store_rows(store, "journal", "id, tenant_id, order_id, account, side, amount_cents"):
    if sqlite_row_get(row, "tenant_id") == "tenant-b":
        b_rows = b_rows + 1
expect(b_rows).to_equal(2)   # tenant B's balanced pair is really in the table

step("Tenant A's report excludes tenant B — totals are A's alone")
val repA = trial_balance(store, session_for("acct-tenant-a", "tenant-a"), tenant("tenant-a"), actor("acct-tenant-a"))
expect(repA.debit_total).to_equal(10000)
expect(repA.credit_total).to_equal(10000)
expect(trial_balance_account(repA, "cash").0).to_equal(10000)

step("Tenant B's report sees only its own 500")
val repB = trial_balance(store, session_for("acct-tenant-b", "tenant-b"), tenant("tenant-b"), actor("acct-tenant-b"))
expect(repB.debit_total).to_equal(500)
expect(repB.credit_total).to_equal(500)
store_close(store)
```

</details>

### finance reporting — imbalance is reported, not hidden (reproduce-first)

#### reports balanced=false for a corrupt single-sided ledger

- reports balanced=false for a corrupt single-sided ledger
- Post one balanced pair for tenant C
- Sanity: the balanced ledger reports balanced
- Simulate ledger corruption: insert a single-sided debit directly (guard cannot produce this)
- Reproduce-first: the extra 999 debit makes debits != credits
   - Expected: bad.debit_total equals `4999`
   - Expected: bad.credit_total equals `4000`
- The report SURFACES the imbalance rather than rendering it as correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports balanced=false for a corrupt single-sided ledger")
val store = setup_store()
step("Post one balanced pair for tenant C")
expect(post(store, "tenant-c", "c1", "inv-c", "cash", "sales_revenue", 4000)).to_be(true)

step("Sanity: the balanced ledger reports balanced")
val ok_rep = trial_balance(store, session_for("acct-tenant-c", "tenant-c"), tenant("tenant-c"), actor("acct-tenant-c"))
expect(ok_rep.balanced).to_be(true)

step("Simulate ledger corruption: insert a single-sided debit directly (guard cannot produce this)")
store_insert_row(store,
    "INSERT INTO journal (tenant_id, order_id, account, side, amount_cents) VALUES (?, ?, ?, ?, ?)",
    ["tenant-c", "corrupt-1", "suspense", "debit", "999"])

step("Reproduce-first: the extra 999 debit makes debits != credits")
val bad = trial_balance(store, session_for("acct-tenant-c", "tenant-c"), tenant("tenant-c"), actor("acct-tenant-c"))
expect(bad.debit_total).to_equal(4999)
expect(bad.credit_total).to_equal(4000)
step("The report SURFACES the imbalance rather than rendering it as correct")
expect(bad.balanced).to_be(false)
store_close(store)
```

</details>

### finance reporting — reads go through the session

#### refuses an inactive session with invalid-session and no data

- refuses an inactive session with invalid-session and no data
- Present an inactive session
   - Expected: rep.reason equals `invalid-session`
   - Expected: rep.debit_total equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses an inactive session with invalid-session and no data")
val store = setup_store()
expect(post(store, "tenant-a", "s1", "inv-1", "cash", "sales_revenue", 10000)).to_be(true)
step("Present an inactive session")
val dead = SessionContext(token: "tok", actor_id: "acct-tenant-a", tenant_id: "tenant-a", active: false)
val rep = trial_balance(store, dead, tenant("tenant-a"), actor("acct-tenant-a"))
expect(rep.ok).to_be(false)
expect(rep.reason).to_equal("invalid-session")
expect(rep.debit_total).to_equal(0)
store_close(store)
```

</details>

### finance reporting — period-scoped variant reads the close snapshot

#### returns the period-boundary totals captured at close

- returns the period-boundary totals captured at close
- Post a balanced pair, then close the period at epoch 200
- Before any close (boundary 50) the period report is no-close
   - Expected: none.reason equals `no-close`
- At boundary 200 the report returns the snapshot totals, balanced
   - Expected: at.debit_total equals `7000`
   - Expected: at.credit_total equals `7000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the period-boundary totals captured at close")
val store = setup_store()
val t = tenant("tenant-a")
val a = actor("acct-tenant-a")
val s = session_for("acct-tenant-a", "tenant-a")
step("Post a balanced pair, then close the period at epoch 200")
expect(post(store, "tenant-a", "p1", "inv-1", "cash", "sales_revenue", 7000)).to_be(true)
val closed = fin_period_close(store, s, t, a, envelope("close-1"), 200, 250)
expect(closed.ok).to_be(true)

step("Before any close (boundary 50) the period report is no-close")
val none = trial_balance_at_close(store, s, t, a, 50)
expect(none.reason).to_equal("no-close")

step("At boundary 200 the report returns the snapshot totals, balanced")
val at = trial_balance_at_close(store, s, t, a, 200)
expect(at.debit_total).to_equal(7000)
expect(at.credit_total).to_equal(7000)
expect(at.balanced).to_be(true)
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
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `825632817a75d6d9bf8c3059b05c0ac97fab6c3e167bbc501c203f07daabb37f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `825632817a75d6d9bf8c3059b05c0ac97fab6c3e167bbc501c203f07daabb37f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `825632817a75d6d9bf8c3059b05c0ac97fab6c3e167bbc501c203f07daabb37f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'folds balanced postings into per-account totals with a balanced ledger' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes another tenant's journal rows from the report' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_finance_reporting_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports balanced=false for a corrupt single-sided ledger' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
