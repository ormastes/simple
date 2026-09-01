# Procurement period seam — receipts must respect finance period close

> Hardening spec for the audit finding in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Procurement period seam — receipts must respect finance period close

Hardening spec for the audit finding in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Source | `test/03_system/app/enterprise/procurement_period_seam_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Hardening spec for the audit finding in
doc/01_research/app/office/office_enterprise_suite_audit_architecture_parallel_plan_2026-08-20.md:
`proc_receive` posted its inventory_asset/accounts_payable journal pair via
RAW `INSERT INTO journal` rows, bypassing the shared period seam
(`records.journal_post_pair`), so a receipt dated inside a CLOSED period was
accepted and mutated the frozen ledger. Pre-fix this spec FAILS (receipt
accepted, journal grows); post-fix the receipt is denied invalid-transition
and writes nothing at all.

## Scenarios

### procurement receipt vs closed finance period

#### denies a PO receipt dated inside a closed period and writes nothing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- denies a PO receipt dated inside a closed period and writes nothing
- Seed supplier -> requisition -> approve -> PO (no receipt yet)
   - Expected: proc_po_create(store, s, t, admin, envelope("po-1-c", "proc.po.create"), "po-1", "req-1", "sup-1", usd(250)).reason equals `accepted`
- Close the tenant's books through the far future
   - Expected: closed.reason equals `accepted`
- A receipt now lands inside the closed period: denied, journal untouched
   - Expected: res.ok is false
   - Expected: res.reason equals `invalid-transition`
   - Expected: journal_rows(store, t.tenant_id) equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("denies a PO receipt dated inside a closed period and writes nothing")
step("Seed supplier -> requisition -> approve -> PO (no receipt yet)")
val store = fresh_store("closed")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
proc_supplier_add(store, s, t, admin, "sup-1", "Supplier One")
proc_requisition_create(store, s, t, admin, envelope("req-1-c", "proc.requisition.create"), "req-1", "SKU-1", 5)
proc_requisition_approve(store, s, t, admin, envelope("req-1-a", "proc.requisition.approve"), "req-1")
expect(proc_po_create(store, s, t, admin, envelope("po-1-c", "proc.po.create"), "po-1", "req-1", "sup-1", usd(250)).reason).to_equal("accepted")

step("Close the tenant's books through the far future")
val closed = fin_period_close(store, s, t, admin, envelope("close-1", "finance.period.close"), far_future(), 1755000000)
expect(closed.reason).to_equal("accepted")

step("A receipt now lands inside the closed period: denied, journal untouched")
val before = journal_rows(store, t.tenant_id)
val res = proc_receive(store, s, t, admin, envelope("po-1-r", "proc.po.receive"), "po-1", 5)
expect(res.ok).to_equal(false)
expect(res.reason).to_equal("invalid-transition")
expect(journal_rows(store, t.tenant_id)).to_equal(before)
store_close(store)
```

</details>

#### accepts the same receipt when no period is closed (control)

- accepts the same receipt when no period is closed (control)
- Same flow, no period close
- Receipt is accepted and posts the balanced pair (2 journal rows)
   - Expected: res.reason equals `accepted`
   - Expected: journal_rows(store, t.tenant_id) equals `before + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts the same receipt when no period is closed (control)")
step("Same flow, no period close")
val store = fresh_store("open")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
proc_supplier_add(store, s, t, admin, "sup-1", "Supplier One")
proc_requisition_create(store, s, t, admin, envelope("req-1-c", "proc.requisition.create"), "req-1", "SKU-1", 5)
proc_requisition_approve(store, s, t, admin, envelope("req-1-a", "proc.requisition.approve"), "req-1")
proc_po_create(store, s, t, admin, envelope("po-1-c", "proc.po.create"), "po-1", "req-1", "sup-1", usd(250))

step("Receipt is accepted and posts the balanced pair (2 journal rows)")
val before = journal_rows(store, t.tenant_id)
val res = proc_receive(store, s, t, admin, envelope("po-1-r", "proc.po.receive"), "po-1", 5)
expect(res.reason).to_equal("accepted")
expect(journal_rows(store, t.tenant_id)).to_equal(before + 2)
store_close(store)
```

</details>

#### neighbor: goods_sale order placement is also denied in a closed period

- neighbor: goods_sale order placement is also denied in a closed period
- Seed product + stock, close the period, then place an order
   - Expected: closed.reason equals `accepted`
   - Expected: res.reason equals `invalid-transition`
   - Expected: journal_rows(store, t.tenant_id) equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("neighbor: goods_sale order placement is also denied in a closed period")
# Defect-class neighbor pin: goods_sale already routes through the seam;
# this keeps the whole journal-writer class covered by one spec file.
step("Seed product + stock, close the period, then place an order")
val store = fresh_store("sale")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_add_product(store, s, t, admin, "SKU-1", "Widget", usd(2500))
sale_receive_stock(store, s, t, admin, "SKU-1", 10)
val closed = fin_period_close(store, s, t, admin, envelope("close-1", "finance.period.close"), far_future(), 1755000000)
expect(closed.reason).to_equal("accepted")
val before = journal_rows(store, t.tenant_id)
val res = sale_place_order(store, s, t, admin, envelope("ord-1", "sale.order.place"), "order-1", "SKU-1", 2)
expect(res.reason).to_equal("invalid-transition")
expect(journal_rows(store, t.tenant_id)).to_equal(before)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cbee73b528130a3c8dab31ea4bf85622ad9ec84d9885bf96382f57e8161ddf24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cbee73b528130a3c8dab31ea4bf85622ad9ec84d9885bf96382f57e8161ddf24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cbee73b528130a3c8dab31ea4bf85622ad9ec84d9885bf96382f57e8161ddf24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/enterprise/procurement_period_seam_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/procurement_period_seam_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/procurement_period_seam_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/procurement_period_seam_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/enterprise/procurement_period_seam_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies a PO receipt dated inside a closed period and writes nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/procurement_period_seam_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the same receipt when no period is closed (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/procurement_period_seam_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'neighbor: goods_sale order placement is also denied in a closed period' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
