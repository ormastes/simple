# Enterprise Back-Office Web — HCM, procurement and finance over the hardened dispatcher

> Lane `.spipe/simple_enterprise_suite` W8-C: the enterprise web app grows the employee/back-office route families `/hcm/*`, `/proc/*` and `/fin/*` — all dispatched through the SAME hardened prelude in `store_app_handle` (limits -> `path_is_safe` -> `session_valid` -> route), executing ONLY the frozen guarded commands of `std.enterprise_hcm`, `std.enterprise_procurement` and `std.enterprise_finance`. No new auth scheme, no new storage, no new guard path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Back-Office Web — HCM, procurement and finance over the hardened dispatcher

Lane `.spipe/simple_enterprise_suite` W8-C: the enterprise web app grows the employee/back-office route families `/hcm/*`, `/proc/*` and `/fin/*` — all dispatched through the SAME hardened prelude in `store_app_handle` (limits -> `path_is_safe` -> `session_valid` -> route), executing ONLY the frozen guarded commands of `std.enterprise_hcm`, `std.enterprise_procurement` and `std.enterprise_finance`. No new auth scheme, no new storage, no new guard path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/back_office_web_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Lane `.spipe/simple_enterprise_suite` W8-C: the enterprise web app grows the
employee/back-office route families `/hcm/*`, `/proc/*` and `/fin/*` — all
dispatched through the SAME hardened prelude in `store_app_handle`
(limits -> `path_is_safe` -> `session_valid` -> route), executing ONLY the
frozen guarded commands of `std.enterprise_hcm`,
`std.enterprise_procurement` and `std.enterprise_finance`. No new auth
scheme, no new storage, no new guard path.

Proven here:
- one end-to-end flow per family through the dispatcher;
- `invalid-session` -> 401 on every new family, before any route logic runs;
- a role lacking the vertical's back-office grant -> 403;
- hostile employee and supplier names are escaped in the rendered pages;
- the admin dashboard's back-office roll-up (employees / open POs / payable
  total / trial-balance balanced) matches an ABSOLUTE hand-computed oracle.

## The dashboard oracle (hand-computed, absolute)

Seed on a clean store: hire `emp-1` and `emp-2`; add supplier `sup-1`;
requisition `rq-1` for 10 units; approve it; raise PO `po-1` at 250
cents/unit (inheriting qty 10 from the requisition); receive 4 units.

- Employees = 2 (two distinct `hired` events).
- Open POs = 1 (`po-1`: received 4 < ordered 10).
- Payable total = 250 * 4 = **1000** cents (`proc_receive` posts one
  balanced `inventory_asset` debit / `accounts_payable` credit pair of
  `unit_cost * qty`; no other payable posting exists in this scenario).
- Trial balance balanced = true (that single pair is the whole journal:
  1000 debit vs 1000 credit).

## Troubleshooting

- Interpreter sqlite caches connections per db PATH — every scenario here
  uses its own db path (see `db_path`).
- `GET /hcm/payroll/export` takes its `[start, end)` window from the same
  digit-checked form parser as every other numeric field, read off the
  request body; an absent window degrades to the full range.
- A raw `<script>` in any rendered body means business data bypassed
  `esc()` — fix the view, never the spec.
- `GET /fin/ap` lists one line per ref that still owes money, derived from
  the shared journal's `accounts_payable` account (credits minus debits);
  the rendered total is the sum of those same lines, so a total that
  disagrees with the lines is impossible by construction.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W8-C).

## Scenarios

### back-office web — HCM family end-to-end through the dispatcher

#### hires, clocks a shift, decides leave, and renders the payroll INPUT export

- Open an hcm-role session on a clean store
- Hire emp-1 — POST /hcm/hire (digit-checked start, wage, hours)
   - Expected: http_status_code(hire.status) equals `200`
   - Expected: hcm_employee_status(store, "tenant-a", "emp-1") equals `active`
- Hiring the same id again with a FRESH key is conflict (409)
   - Expected: http_status_code(again.status) equals `409`
- A non-numeric wage is digit-rejected to 0 and denied invalid-record (409)
   - Expected: http_status_code(bad.status) equals `409`
- Clock in at 1000 and out at 4600 — one closed 3600s interval
   - Expected: http_status_code(cin.status) equals `200`
   - Expected: http_status_code(cout.status) equals `200`
   - Expected: hcm_worked_seconds(store, "tenant-a", "emp-1", 0, 400000) equals `3600`
- Request one day of leave and approve it
   - Expected: http_status_code(req.status) equals `200`
   - Expected: http_status_code(decide.status) equals `200`
   - Expected: hcm_leave_status(store, "tenant-a", "lv-1") equals `approved`
- GET /hcm/employees shows the roster with the current wage
   - Expected: http_status_code(roster.status) equals `200`
- GET /hcm/payroll/export renders the boundary table, labelled as INPUT
   - Expected: http_status_code(payroll.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open an hcm-role session on a clean store")
val store = fresh_back_office("hcm")
val t = tenant_a()
val hr = ActorContext(actor_id: "hr-1", role: "hcm")
val s = session_for(hr, t)

step("Hire emp-1 — POST /hcm/hire (digit-checked start, wage, hours)")
val hire = store_app_handle(store, s, t, hr, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-1&name=Ada&start=0&wage=2000&hours=40&idem=hire-1")
expect(http_status_code(hire.status)).to_equal(200)
expect(hcm_employee_status(store, "tenant-a", "emp-1")).to_equal("active")

step("Hiring the same id again with a FRESH key is conflict (409)")
val again = store_app_handle(store, s, t, hr, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-1&name=Ada&start=0&wage=2000&hours=40&idem=hire-2")
expect(http_status_code(again.status)).to_equal(409)
expect(again.body.contains("conflict")).to_be(true)

step("A non-numeric wage is digit-rejected to 0 and denied invalid-record (409)")
val bad = store_app_handle(store, s, t, hr, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-9&name=Bad&start=0&wage=20x0&hours=40&idem=hire-9")
expect(http_status_code(bad.status)).to_equal(409)
expect(bad.body.contains("invalid-record")).to_be(true)

step("Clock in at 1000 and out at 4600 — one closed 3600s interval")
val cin = store_app_handle(store, s, t, hr, "POST", "/hcm/clock/in", plain_headers(),
    "employee=emp-1&now=1000&idem=in-1")
expect(http_status_code(cin.status)).to_equal(200)
val cout = store_app_handle(store, s, t, hr, "POST", "/hcm/clock/out", plain_headers(),
    "employee=emp-1&now=4600&idem=out-1")
expect(http_status_code(cout.status)).to_equal(200)
expect(hcm_worked_seconds(store, "tenant-a", "emp-1", 0, 400000)).to_equal(3600)

step("Request one day of leave and approve it")
val req = store_app_handle(store, s, t, hr, "POST", "/hcm/leave/request", plain_headers(),
    "leave=lv-1&employee=emp-1&start=200000&end=286400&type=annual&idem=lv-req-1")
expect(http_status_code(req.status)).to_equal(200)
val decide = store_app_handle(store, s, t, hr, "POST", "/hcm/leave/decide", plain_headers(),
    "leave=lv-1&approve=1&idem=lv-dec-1")
expect(http_status_code(decide.status)).to_equal(200)
expect(hcm_leave_status(store, "tenant-a", "lv-1")).to_equal("approved")

step("GET /hcm/employees shows the roster with the current wage")
val roster = store_app_handle(store, s, t, hr, "GET", "/hcm/employees", plain_headers(), "")
expect(http_status_code(roster.status)).to_equal(200)
expect(roster.body.contains("class=\"emp-id\">emp-1</span>")).to_be(true)
expect(roster.body.contains("class=\"emp-status\">active</span>")).to_be(true)
expect(roster.body.contains("class=\"emp-wage\">2000</span>")).to_be(true)

step("GET /hcm/payroll/export renders the boundary table, labelled as INPUT")
val payroll = store_app_handle(store, s, t, hr, "GET", "/hcm/payroll/export", plain_headers(),
    "start=0&end=400000")
expect(http_status_code(payroll.status)).to_equal(200)
expect(payroll.body.contains("NOT a payslip")).to_be(true)
expect(payroll.body.contains("class=\"wage\">2000</td>")).to_be(true)
expect(payroll.body.contains("class=\"worked\">3600</td>")).to_be(true)
expect(payroll.body.contains("class=\"leave\">1</td>")).to_be(true)
store_close(store)
```

</details>

### back-office web — procurement family end-to-end through the dispatcher

#### requisitions, approves, raises a PO, receives, invoices, and reconciles

- Seed a supplier as admin, then act as a procurement-role session
- Create requisition rq-1 for 10 units — POST /proc/requisition
   - Expected: http_status_code(rq.status) equals `200`
   - Expected: proc_requisition_status(store, "tenant-a", "rq-1") equals `created`
- A PO on an unapproved requisition is invalid-transition (409)
   - Expected: http_status_code(early.status) equals `409`
- Approve the requisition — POST /proc/requisition/approve
   - Expected: http_status_code(ap.status) equals `200`
   - Expected: proc_requisition_status(store, "tenant-a", "rq-1") equals `approved`
- An unknown supplier is not-found (404)
   - Expected: http_status_code(nosup.status) equals `404`
- Raise PO po-1 at 250 cents/unit — POST /proc/po
   - Expected: http_status_code(po.status) equals `200`
- Receive 4 of the 10 ordered — POST /proc/receive
   - Expected: http_status_code(rcv.status) equals `200`
   - Expected: proc_po_received(store, "tenant-a", "po-1") equals `4`
- Over-receipt beyond the ordered quantity is insufficient-stock (409)
   - Expected: http_status_code(over.status) equals `409`
- Invoice the 4 received units — POST /proc/invoice
   - Expected: http_status_code(inv.status) equals `200`
   - Expected: proc_po_invoiced(store, "tenant-a", "po-1") equals `4`
- GET /proc/pos lists po-1 as still open (4 of 10 received)
   - Expected: http_status_code(pos.status) equals `200`
- GET /proc/reconcile reports the three-way position
   - Expected: http_status_code(rec.status) equals `200`
   - Expected: proc_payable_total(store, "tenant-a") equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed a supplier as admin, then act as a procurement-role session")
val store = fresh_back_office("proc")
val t = tenant_a()
val admin = admin_a()
proc_supplier_add(store, session_for(admin, t), t, admin, "sup-1", "ACME Supply")
val buyer = ActorContext(actor_id: "buyer-1", role: "procurement")
val s = session_for(buyer, t)

step("Create requisition rq-1 for 10 units — POST /proc/requisition")
val rq = store_app_handle(store, s, t, buyer, "POST", "/proc/requisition", plain_headers(),
    "req=rq-1&sku=SKU-P&qty=10&idem=rq-1")
expect(http_status_code(rq.status)).to_equal(200)
expect(proc_requisition_status(store, "tenant-a", "rq-1")).to_equal("created")

step("A PO on an unapproved requisition is invalid-transition (409)")
val early = store_app_handle(store, s, t, buyer, "POST", "/proc/po", plain_headers(),
    "po=po-early&req=rq-1&supplier=sup-1&cost=250&idem=po-early")
expect(http_status_code(early.status)).to_equal(409)
expect(early.body.contains("invalid-transition")).to_be(true)

step("Approve the requisition — POST /proc/requisition/approve")
val ap = store_app_handle(store, s, t, buyer, "POST", "/proc/requisition/approve", plain_headers(),
    "req=rq-1&idem=ap-1")
expect(http_status_code(ap.status)).to_equal(200)
expect(proc_requisition_status(store, "tenant-a", "rq-1")).to_equal("approved")

step("An unknown supplier is not-found (404)")
val nosup = store_app_handle(store, s, t, buyer, "POST", "/proc/po", plain_headers(),
    "po=po-x&req=rq-1&supplier=ghost&cost=250&idem=po-x")
expect(http_status_code(nosup.status)).to_equal(404)

step("Raise PO po-1 at 250 cents/unit — POST /proc/po")
val po = store_app_handle(store, s, t, buyer, "POST", "/proc/po", plain_headers(),
    "po=po-1&req=rq-1&supplier=sup-1&cost=250&idem=po-1")
expect(http_status_code(po.status)).to_equal(200)

step("Receive 4 of the 10 ordered — POST /proc/receive")
val rcv = store_app_handle(store, s, t, buyer, "POST", "/proc/receive", plain_headers(),
    "po=po-1&qty=4&idem=rcv-1")
expect(http_status_code(rcv.status)).to_equal(200)
expect(proc_po_received(store, "tenant-a", "po-1")).to_equal(4)

step("Over-receipt beyond the ordered quantity is insufficient-stock (409)")
val over = store_app_handle(store, s, t, buyer, "POST", "/proc/receive", plain_headers(),
    "po=po-1&qty=99&idem=rcv-over")
expect(http_status_code(over.status)).to_equal(409)
expect(over.body.contains("insufficient-stock")).to_be(true)

step("Invoice the 4 received units — POST /proc/invoice")
val inv = store_app_handle(store, s, t, buyer, "POST", "/proc/invoice", plain_headers(),
    "po=po-1&invoice=inv-1&qty=4&idem=inv-1")
expect(http_status_code(inv.status)).to_equal(200)
expect(proc_po_invoiced(store, "tenant-a", "po-1")).to_equal(4)

step("GET /proc/pos lists po-1 as still open (4 of 10 received)")
val pos = store_app_handle(store, s, t, buyer, "GET", "/proc/pos", plain_headers(), "")
expect(http_status_code(pos.status)).to_equal(200)
expect(pos.body.contains("class=\"po-id\">po-1</span>")).to_be(true)
expect(pos.body.contains("class=\"po-ordered\">10</span>")).to_be(true)
expect(pos.body.contains("class=\"po-received\">4</span>")).to_be(true)
expect(pos.body.contains("class=\"po-invoiced\">4</span>")).to_be(true)

step("GET /proc/reconcile reports the three-way position")
val rec = store_app_handle(store, s, t, buyer, "GET", "/proc/reconcile", plain_headers(), "")
expect(http_status_code(rec.status)).to_equal(200)
expect(rec.body.contains("class=\"open_pos\">1</span>")).to_be(true)
expect(rec.body.contains("class=\"fully_invoiced\">1</span>")).to_be(true)
expect(rec.body.contains("class=\"payable_cents\">1000</span>")).to_be(true)
expect(proc_payable_total(store, "tenant-a")).to_equal(1000)
store_close(store)
```

</details>

### back-office web — finance family end-to-end through the dispatcher

#### reports the trial balance, AR, AP, then closes and reports a period

- Seed one balanced payable pair through the procurement routes
   - Expected: http_status_code(rcv.status) equals `200`
- GET /fin/trial-balance shows both accounts and the balanced flag
   - Expected: http_status_code(tb.status) equals `200`
- GET /fin/ar is empty — no order was placed in this scenario
   - Expected: http_status_code(ar.status) equals `200`
- GET /fin/ap lists the po-f line AND a total that agrees with it
   - Expected: http_status_code(ap.status) equals `200`
- Before any close, GET /fin/period/status reports 0
   - Expected: http_status_code(before.status) equals `200`
- POST /fin/period/close closes the books through epoch 5000
   - Expected: http_status_code(close.status) equals `200`
   - Expected: fin_period_status(store, "tenant-a") equals `5000`
- GET /fin/period/status now reports the close and its captured totals
   - Expected: http_status_code(after.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed one balanced payable pair through the procurement routes")
val store = fresh_back_office("fin")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
proc_supplier_add(store, s, t, admin, "sup-1", "ACME Supply")
store_app_handle(store, s, t, admin, "POST", "/proc/requisition", plain_headers(),
    "req=rq-f&sku=SKU-F&qty=10&idem=f-rq")
store_app_handle(store, s, t, admin, "POST", "/proc/requisition/approve", plain_headers(),
    "req=rq-f&idem=f-ap")
store_app_handle(store, s, t, admin, "POST", "/proc/po", plain_headers(),
    "po=po-f&req=rq-f&supplier=sup-1&cost=250&idem=f-po")
val rcv = store_app_handle(store, s, t, admin, "POST", "/proc/receive", plain_headers(),
    "po=po-f&qty=4&idem=f-rcv")
expect(http_status_code(rcv.status)).to_equal(200)

step("GET /fin/trial-balance shows both accounts and the balanced flag")
val tb = store_app_handle(store, s, t, admin, "GET", "/fin/trial-balance", plain_headers(), "")
expect(http_status_code(tb.status)).to_equal(200)
expect(tb.body.contains("class=\"debit-total\">1000</span>")).to_be(true)
expect(tb.body.contains("class=\"credit-total\">1000</span>")).to_be(true)
expect(tb.body.contains("class=\"balanced\">true</span>")).to_be(true)
expect(fin_trial_balance(store, "tenant-a").balanced).to_be(true)

step("GET /fin/ar is empty — no order was placed in this scenario")
val ar = store_app_handle(store, s, t, admin, "GET", "/fin/ar", plain_headers(), "")
expect(http_status_code(ar.status)).to_equal(200)
expect(ar.body.contains("class=\"ar-total\">0</span>")).to_be(true)

step("GET /fin/ap lists the po-f line AND a total that agrees with it")
val ap = store_app_handle(store, s, t, admin, "GET", "/fin/ap", plain_headers(), "")
expect(http_status_code(ap.status)).to_equal(200)
expect(ap.body.contains("data-ref=\"po-f\"")).to_be(true)
expect(ap.body.contains("class=\"amount\">1000</span>")).to_be(true)
expect(ap.body.contains("class=\"ap-total\">1000</span>")).to_be(true)

step("Before any close, GET /fin/period/status reports 0")
val before = store_app_handle(store, s, t, admin, "GET", "/fin/period/status", plain_headers(), "")
expect(http_status_code(before.status)).to_equal(200)
expect(before.body.contains("class=\"period-end\">0</span>")).to_be(true)

step("POST /fin/period/close closes the books through epoch 5000")
val close = store_app_handle(store, s, t, admin, "POST", "/fin/period/close", plain_headers(),
    "end=5000&now=6000&idem=close-1")
expect(http_status_code(close.status)).to_equal(200)
expect(fin_period_status(store, "tenant-a")).to_equal(5000)

step("GET /fin/period/status now reports the close and its captured totals")
val after = store_app_handle(store, s, t, admin, "GET", "/fin/period/status", plain_headers(), "")
expect(http_status_code(after.status)).to_equal(200)
expect(after.body.contains("class=\"period-end\">5000</span>")).to_be(true)
expect(after.body.contains("class=\"close-debit\">1000</span>")).to_be(true)
expect(after.body.contains("class=\"close-credit\">1000</span>")).to_be(true)
store_close(store)
```

</details>

### back-office web — unauthenticated denial on every new route family

#### an inactive session gets 401 before any route logic runs

- HCM family — GET /hcm/employees is 401
   - Expected: http_status_code(h.status) equals `401`
- HCM family — POST /hcm/hire is 401
   - Expected: http_status_code(hw.status) equals `401`
- Procurement family — GET /proc/pos is 401
   - Expected: http_status_code(p.status) equals `401`
- Procurement family — POST /proc/requisition is 401
   - Expected: http_status_code(pw.status) equals `401`
- Finance family — GET /fin/trial-balance is 401
   - Expected: http_status_code(f.status) equals `401`
- Finance family — POST /fin/period/close is 401
   - Expected: http_status_code(fw.status) equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_back_office("unauth")
val t = tenant_a()
val admin = admin_a()
val dead = SessionContext(token: "tok-dead", actor_id: admin.actor_id, tenant_id: t.tenant_id, active: false)

step("HCM family — GET /hcm/employees is 401")
val h = store_app_handle(store, dead, t, admin, "GET", "/hcm/employees", plain_headers(), "")
expect(http_status_code(h.status)).to_equal(401)

step("HCM family — POST /hcm/hire is 401")
val hw = store_app_handle(store, dead, t, admin, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-u&name=U&start=0&wage=100&hours=40&idem=u-1")
expect(http_status_code(hw.status)).to_equal(401)

step("Procurement family — GET /proc/pos is 401")
val p = store_app_handle(store, dead, t, admin, "GET", "/proc/pos", plain_headers(), "")
expect(http_status_code(p.status)).to_equal(401)

step("Procurement family — POST /proc/requisition is 401")
val pw = store_app_handle(store, dead, t, admin, "POST", "/proc/requisition", plain_headers(),
    "req=rq-u&sku=SKU-U&qty=1&idem=u-2")
expect(http_status_code(pw.status)).to_equal(401)

step("Finance family — GET /fin/trial-balance is 401")
val f = store_app_handle(store, dead, t, admin, "GET", "/fin/trial-balance", plain_headers(), "")
expect(http_status_code(f.status)).to_equal(401)

step("Finance family — POST /fin/period/close is 401")
val fw = store_app_handle(store, dead, t, admin, "POST", "/fin/period/close", plain_headers(),
    "end=100&now=200&idem=u-3")
expect(http_status_code(fw.status)).to_equal(401)
store_close(store)
```

</details>

### back-office web — a role lacking the vertical grant is denied 403

#### a sales-role session is forbidden on every new family, read and write

- HCM read and write are both 403 for the sales role
   - Expected: http_status_code(hr_read.status) equals `403`
   - Expected: http_status_code(hr_write.status) equals `403`
- Procurement read and write are both 403 for the sales role
   - Expected: http_status_code(p_read.status) equals `403`
   - Expected: http_status_code(p_write.status) equals `403`
- Finance read and write are both 403 for the sales role
   - Expected: http_status_code(f_read.status) equals `403`
   - Expected: http_status_code(f_write.status) equals `403`
- Every denial names the frozen `forbidden` reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_back_office("rbac")
val t = tenant_a()
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val s = session_for(clerk, t)

step("HCM read and write are both 403 for the sales role")
val hr_read = store_app_handle(store, s, t, clerk, "GET", "/hcm/employees", plain_headers(), "")
expect(http_status_code(hr_read.status)).to_equal(403)
val hr_write = store_app_handle(store, s, t, clerk, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-r&name=R&start=0&wage=100&hours=40&idem=r-1")
expect(http_status_code(hr_write.status)).to_equal(403)

step("Procurement read and write are both 403 for the sales role")
val p_read = store_app_handle(store, s, t, clerk, "GET", "/proc/pos", plain_headers(), "")
expect(http_status_code(p_read.status)).to_equal(403)
val p_write = store_app_handle(store, s, t, clerk, "POST", "/proc/requisition", plain_headers(),
    "req=rq-r&sku=SKU-R&qty=1&idem=r-2")
expect(http_status_code(p_write.status)).to_equal(403)

step("Finance read and write are both 403 for the sales role")
val f_read = store_app_handle(store, s, t, clerk, "GET", "/fin/trial-balance", plain_headers(), "")
expect(http_status_code(f_read.status)).to_equal(403)
val f_write = store_app_handle(store, s, t, clerk, "POST", "/fin/period/close", plain_headers(),
    "end=100&now=200&idem=r-3")
expect(http_status_code(f_write.status)).to_equal(403)

step("Every denial names the frozen `forbidden` reason")
expect(hr_read.body.contains("forbidden")).to_be(true)
expect(p_write.body.contains("forbidden")).to_be(true)
expect(f_read.body.contains("forbidden")).to_be(true)
store_close(store)
```

</details>

### back-office web — hostile business data is escaped, never rendered raw

#### a script-tag employee name and supplier name come back escaped

- Hire an employee whose NAME is a script tag
   - Expected: http_status_code(hire.status) equals `200`
- GET /hcm/employees escapes it — no raw tag survives
   - Expected: http_status_code(roster.status) equals `200`
- Register a supplier whose NAME is a script tag, and open a PO on it
   - Expected: http_status_code(po.status) equals `200`
- GET /proc/pos escapes the supplier name — no raw tag survives
   - Expected: http_status_code(pos.status) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_back_office("escape")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)

step("Hire an employee whose NAME is a script tag")
val hire = store_app_handle(store, s, t, admin, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-x&name=<script>alert(1)</script>&start=0&wage=100&hours=40&idem=x-1")
expect(http_status_code(hire.status)).to_equal(200)

step("GET /hcm/employees escapes it — no raw tag survives")
val roster = store_app_handle(store, s, t, admin, "GET", "/hcm/employees", plain_headers(), "")
expect(http_status_code(roster.status)).to_equal(200)
expect(roster.body.contains("&lt;script&gt;")).to_be(true)
expect(roster.body.contains("<script>alert")).to_be(false)

step("Register a supplier whose NAME is a script tag, and open a PO on it")
proc_supplier_add(store, s, t, admin, "sup-x", "<script>alert(2)</script>")
store_app_handle(store, s, t, admin, "POST", "/proc/requisition", plain_headers(),
    "req=rq-x&sku=SKU-X&qty=5&idem=x-2")
store_app_handle(store, s, t, admin, "POST", "/proc/requisition/approve", plain_headers(),
    "req=rq-x&idem=x-3")
val po = store_app_handle(store, s, t, admin, "POST", "/proc/po", plain_headers(),
    "po=po-x&req=rq-x&supplier=sup-x&cost=100&idem=x-4")
expect(http_status_code(po.status)).to_equal(200)

step("GET /proc/pos escapes the supplier name — no raw tag survives")
val pos = store_app_handle(store, s, t, admin, "GET", "/proc/pos", plain_headers(), "")
expect(http_status_code(pos.status)).to_equal(200)
expect(pos.body.contains("&lt;script&gt;alert(2)&lt;/script&gt;")).to_be(true)
expect(pos.body.contains("<script>alert(2)")).to_be(false)
store_close(store)
```

</details>

### back-office web — the dashboard back-office roll-up

#### matches the absolute hand-computed oracle: 2 employees, 1 open PO, 1000 payable, balanced

- Seed exactly the oracle scenario (see the spec header)
   - Expected: http_status_code(h1.status) equals `200`
   - Expected: http_status_code(h2.status) equals `200`
   - Expected: http_status_code(rcv.status) equals `200`
- GET /admin/dashboard as admin carries the four roll-up figures
   - Expected: http_status_code(dash.status) equals `200`
- The oracle is corroborated by the libraries directly
   - Expected: proc_payable_total(store, "tenant-a") equals `1000`
   - Expected: proc_po_received(store, "tenant-a", "po-1") equals `4`
- A sales-role session still cannot read the dashboard (403)
   - Expected: http_status_code(denied.status) equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed exactly the oracle scenario (see the spec header)")
val store = fresh_back_office("rollup")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
val h1 = store_app_handle(store, s, t, admin, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-1&name=Ada&start=0&wage=2000&hours=40&idem=r-h1")
expect(http_status_code(h1.status)).to_equal(200)
val h2 = store_app_handle(store, s, t, admin, "POST", "/hcm/hire", plain_headers(),
    "employee=emp-2&name=Bo&start=0&wage=2500&hours=40&idem=r-h2")
expect(http_status_code(h2.status)).to_equal(200)
proc_supplier_add(store, s, t, admin, "sup-1", "ACME Supply")
store_app_handle(store, s, t, admin, "POST", "/proc/requisition", plain_headers(),
    "req=rq-1&sku=SKU-P&qty=10&idem=r-rq")
store_app_handle(store, s, t, admin, "POST", "/proc/requisition/approve", plain_headers(),
    "req=rq-1&idem=r-ap")
store_app_handle(store, s, t, admin, "POST", "/proc/po", plain_headers(),
    "po=po-1&req=rq-1&supplier=sup-1&cost=250&idem=r-po")
val rcv = store_app_handle(store, s, t, admin, "POST", "/proc/receive", plain_headers(),
    "po=po-1&qty=4&idem=r-rcv")
expect(http_status_code(rcv.status)).to_equal(200)

step("GET /admin/dashboard as admin carries the four roll-up figures")
val dash = store_app_handle(store, s, t, admin, "GET", "/admin/dashboard", plain_headers(), "")
expect(http_status_code(dash.status)).to_equal(200)
expect(dash.body.contains("class=\"employees\">2</span>")).to_be(true)
expect(dash.body.contains("class=\"open-pos\">1</span>")).to_be(true)
expect(dash.body.contains("class=\"payable-total\">1000</span>")).to_be(true)
expect(dash.body.contains("class=\"tb-balanced\">true</span>")).to_be(true)

step("The oracle is corroborated by the libraries directly")
expect(proc_payable_total(store, "tenant-a")).to_equal(1000)
expect(proc_po_received(store, "tenant-a", "po-1")).to_equal(4)
expect(fin_trial_balance(store, "tenant-a").balanced).to_be(true)

step("A sales-role session still cannot read the dashboard (403)")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val denied = store_app_handle(store, session_for(clerk, t), t, clerk, "GET", "/admin/dashboard", plain_headers(), "")
expect(http_status_code(denied.status)).to_equal(403)
store_close(store)
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
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>
