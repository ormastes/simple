# Guarded-Command Conformance — one contract, every enterprise vertical

> The enterprise suite has many vertical modules that each copy ONE frozen guarded-write sequence:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guarded-Command Conformance — one contract, every enterprise vertical

The enterprise suite has many vertical modules that each copy ONE frozen guarded-write sequence:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md |
| Design | doc/07_guide/app/enterprise/guarded_command_contract.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The enterprise suite has many vertical modules that each copy ONE frozen
guarded-write sequence:

    session -> rbac -> validation -> idempotency -> effects in one UoW

They were written by different lanes at different times, so they drift. This
spec is the executable conformance gate for that contract. It does NOT read
module source text — source-text/grep assertions are banned as evidence in
this repo. Every invariant here is proven by DRIVING the real commands
against a real store and reading the resulting rows.

Invariants exercised, across booking, restaurant, payment, HCM, procurement,
channel-hub, outbox-worker, session, and goods-sale:

1. **Replay returns the recorded result, not a re-evaluation.** Every guarded
   command is run twice with the SAME idempotency key. The second call must
   answer `duplicate-key` carrying the recorded detail — never a denial
   produced by re-checking state that the command's own first execution
   changed. This is the exact defect class already found in procurement and
   goods_sale (state-dependent feasibility evaluated before replay detection).
2. **Exactly one effect.** The outbox+audit row fingerprint for the tenant is
   captured after the first call and must be byte-identical after the replay.
3. **Closed reason set.** Every reason any command returns — accepted or
   denied — must satisfy `reason_allowed` from `enterprise_sale.foundation`.
   That predicate IS the closed set; prose is not the oracle.
4. **Tenant scoping.** A session issued for tenant B is denied by every
   command in every module when tenant A is the authoritative tenant.

## Deliberate scope gap

`sale_pay_order` / `sale_refund_order` / `sale_place_order` replay rows are
NOT asserted here: `enterprise_sale/goods_sale.spl` is owned by lane W7-A
while it lands the same ordering fix. goods_sale still participates in the
closed-reason-set and tenant-scoping scenarios. Add the three replay
assertions to the replay scenarios once W7-A lands — see
doc/07_guide/app/enterprise/guarded_command_contract.md.

## Troubleshooting

- A replay answering `invalid-transition`, `conflict`, `table-occupied`,
  `session-closed`, `invalid-record`, or `insufficient-stock` instead of
  `duplicate-key` is THE drift this spec exists to catch: a state-dependent
  rung is being evaluated before replay detection. Gate that rung behind
  `if not replayed:` — identity checks (not-found) stay unconditional.
- A changed effect fingerprint means the replay wrote a second effect.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md
**Design:** doc/07_guide/app/enterprise/guarded_command_contract.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W7-B).

## Scenarios

### guarded-command conformance — replay returns the recorded result

#### booking: hold, confirm, cancel, and no-show replay to duplicate-key with one effect

- Seed two exclusive-unit resources
   - Expected: booking_create_resource(store, s, t, admin, "res-1", "exclusive-unit", 1, "v1").reason equals `accepted`
   - Expected: booking_create_resource(store, s, t, admin, "res-2", "exclusive-unit", 1, "v1").reason equals `accepted`
- hold: first call accepted, replay of the SAME key is duplicate-key
   - Expected: booking_hold(store, s, t, admin, envelope("bk-hold"), "bk-1", "res-1", 100, 200, 1, "", 50, 1000).reason equals `accepted`
   - Expected: hold_replay.reason equals `duplicate-key`
   - Expected: hold_replay.detail equals `bk-1`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_hold`
- confirm: the confirmed status must not be re-checked on replay
   - Expected: booking_confirm(store, s, t, admin, envelope("bk-conf"), "bk-1", 60).reason equals `accepted`
   - Expected: conf_replay.reason equals `duplicate-key`
   - Expected: conf_replay.detail equals `bk-1`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_conf`
- cancel: the cancelled status must not be re-checked on replay
   - Expected: booking_cancel(store, s, t, admin, envelope("bk-can"), "bk-1").reason equals `accepted`
   - Expected: booking_cancel(store, s, t, admin, envelope("bk-can"), "bk-1").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_can`
- no-show on a second booking: replays to duplicate-key
   - Expected: booking_no_show(store, s, t, admin, envelope("bk-ns"), "bk-2").reason equals `accepted`
   - Expected: booking_no_show(store, s, t, admin, envelope("bk-ns"), "bk-2").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_ns`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed two exclusive-unit resources")
val store = fresh_store("booking")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
booking_setup(store)
expect(booking_create_resource(store, s, t, admin, "res-1", "exclusive-unit", 1, "v1").reason).to_equal("accepted")
expect(booking_create_resource(store, s, t, admin, "res-2", "exclusive-unit", 1, "v1").reason).to_equal("accepted")

step("hold: first call accepted, replay of the SAME key is duplicate-key")
expect(booking_hold(store, s, t, admin, envelope("bk-hold"), "bk-1", "res-1", 100, 200, 1, "", 50, 1000).reason).to_equal("accepted")
val fp_hold = effect_fingerprint(store, "tenant-a")
val hold_replay = booking_hold(store, s, t, admin, envelope("bk-hold"), "bk-1", "res-1", 100, 200, 1, "", 50, 1000)
expect(hold_replay.reason).to_equal("duplicate-key")
expect(hold_replay.detail).to_equal("bk-1")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_hold)

step("confirm: the confirmed status must not be re-checked on replay")
expect(booking_confirm(store, s, t, admin, envelope("bk-conf"), "bk-1", 60).reason).to_equal("accepted")
val fp_conf = effect_fingerprint(store, "tenant-a")
val conf_replay = booking_confirm(store, s, t, admin, envelope("bk-conf"), "bk-1", 60)
expect(conf_replay.reason).to_equal("duplicate-key")
expect(conf_replay.detail).to_equal("bk-1")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_conf)

step("cancel: the cancelled status must not be re-checked on replay")
expect(booking_cancel(store, s, t, admin, envelope("bk-can"), "bk-1").reason).to_equal("accepted")
val fp_can = effect_fingerprint(store, "tenant-a")
expect(booking_cancel(store, s, t, admin, envelope("bk-can"), "bk-1").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_can)

step("no-show on a second booking: replays to duplicate-key")
booking_hold(store, s, t, admin, envelope("bk-hold2"), "bk-2", "res-2", 100, 200, 1, "", 50, 1000)
booking_confirm(store, s, t, admin, envelope("bk-conf2"), "bk-2", 60)
expect(booking_no_show(store, s, t, admin, envelope("bk-ns"), "bk-2").reason).to_equal("accepted")
val fp_ns = effect_fingerprint(store, "tenant-a")
expect(booking_no_show(store, s, t, admin, envelope("bk-ns"), "bk-2").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_ns)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### restaurant: open, add-line, ready, serve, and close replay to duplicate-key with one effect

- Seed the venue and one menu item
- open the table session; the table it occupies is its OWN effect
   - Expected: table_open_session(store, s, t, admin, envelope("rs-open"), "sess-1", "v1", "t1", 2).reason equals `accepted`
   - Expected: open_replay.reason equals `duplicate-key`
   - Expected: open_replay.detail equals `sess-1`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_open`
- add-line replays (already fixed upstream — regression fence)
   - Expected: order_add_line(store, s, t, admin, envelope("rs-line"), "sess-1", "line-1", "SKU-1", 2, "").reason equals `accepted`
   - Expected: order_add_line(store, s, t, admin, envelope("rs-line"), "sess-1", "line-1", "SKU-1", 2, "").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_line`
- kitchen ready: the line's new state must not be re-checked on replay
   - Expected: kitchen_mark_ready(store, s, t, admin, envelope("rs-ready"), "sess-1", "line-1").reason equals `accepted`
   - Expected: kitchen_mark_ready(store, s, t, admin, envelope("rs-ready"), "sess-1", "line-1").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_ready`
- serve: same forward-only transition, same replay rule
   - Expected: line_mark_served(store, s, t, admin, envelope("rs-serve"), "sess-1", "line-1").reason equals `accepted`
   - Expected: line_mark_served(store, s, t, admin, envelope("rs-serve"), "sess-1", "line-1").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_serve`
- bill close: the session it closes is its own effect; detail is the total
   - Expected: closed.reason equals `accepted`
   - Expected: closed.detail equals `1000`
   - Expected: close_replay.reason equals `duplicate-key`
   - Expected: close_replay.detail equals `1000`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_close`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed the venue and one menu item")
val store = fresh_store("restaurant")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
restaurant_setup(store)
sale_add_product(store, s, t, admin, "SKU-1", "Soup", usd(500))

step("open the table session; the table it occupies is its OWN effect")
expect(table_open_session(store, s, t, admin, envelope("rs-open"), "sess-1", "v1", "t1", 2).reason).to_equal("accepted")
val fp_open = effect_fingerprint(store, "tenant-a")
val open_replay = table_open_session(store, s, t, admin, envelope("rs-open"), "sess-1", "v1", "t1", 2)
expect(open_replay.reason).to_equal("duplicate-key")
expect(open_replay.detail).to_equal("sess-1")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_open)

step("add-line replays (already fixed upstream — regression fence)")
expect(order_add_line(store, s, t, admin, envelope("rs-line"), "sess-1", "line-1", "SKU-1", 2, "").reason).to_equal("accepted")
val fp_line = effect_fingerprint(store, "tenant-a")
expect(order_add_line(store, s, t, admin, envelope("rs-line"), "sess-1", "line-1", "SKU-1", 2, "").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_line)

step("kitchen ready: the line's new state must not be re-checked on replay")
expect(kitchen_mark_ready(store, s, t, admin, envelope("rs-ready"), "sess-1", "line-1").reason).to_equal("accepted")
val fp_ready = effect_fingerprint(store, "tenant-a")
expect(kitchen_mark_ready(store, s, t, admin, envelope("rs-ready"), "sess-1", "line-1").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_ready)

step("serve: same forward-only transition, same replay rule")
expect(line_mark_served(store, s, t, admin, envelope("rs-serve"), "sess-1", "line-1").reason).to_equal("accepted")
val fp_serve = effect_fingerprint(store, "tenant-a")
expect(line_mark_served(store, s, t, admin, envelope("rs-serve"), "sess-1", "line-1").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_serve)

step("bill close: the session it closes is its own effect; detail is the total")
val closed = bill_close_session(store, s, t, admin, envelope("rs-close"), "sess-1")
expect(closed.reason).to_equal("accepted")
expect(closed.detail).to_equal("1000")
val fp_close = effect_fingerprint(store, "tenant-a")
val close_replay = bill_close_session(store, s, t, admin, envelope("rs-close"), "sess-1")
expect(close_replay.reason).to_equal("duplicate-key")
expect(close_replay.detail).to_equal("1000")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_close)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### payment: intent-create and captured webhook replay to duplicate-key with one effect

- Seed a created, stocked order
   - Expected: sale_place_order(store, s, t, admin, envelope("py-ord"), "order-1", "SKU-1", 1).reason equals `accepted`
- intent create: the pending intent it writes is its own effect
   - Expected: intent.reason equals `accepted`
   - Expected: intent.detail equals `prov-tenant-a-int-1`
   - Expected: intent_replay.reason equals `duplicate-key`
   - Expected: intent_replay.detail equals `prov-tenant-a-int-1`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_int`
- captured webhook replays on provider_event_id (already fixed — regression fence)
   - Expected: payment_webhook_receive(store, s, t, admin, env_wh, provider, "prov-tenant-a-int-1", "captured", sig, "evt-1", 200).reason equals `accepted`
   - Expected: wh_replay.reason equals `duplicate-key`
   - Expected: wh_replay.detail equals `int-1:captured`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_wh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed a created, stocked order")
val store = fresh_store("payment")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_setup(store)
payment_setup(store)
sale_add_product(store, s, t, admin, "SKU-1", "Widget", usd(2500))
sale_receive_stock(store, s, t, admin, "SKU-1", 10)
expect(sale_place_order(store, s, t, admin, envelope("py-ord"), "order-1", "SKU-1", 1).reason).to_equal("accepted")

step("intent create: the pending intent it writes is its own effect")
val intent = payment_create_intent(store, s, t, admin, envelope("py-int"), "int-1", "order-1", 100)
expect(intent.reason).to_equal("accepted")
expect(intent.detail).to_equal("prov-tenant-a-int-1")
val fp_int = effect_fingerprint(store, "tenant-a")
val intent_replay = payment_create_intent(store, s, t, admin, envelope("py-int"), "int-1", "order-1", 100)
expect(intent_replay.reason).to_equal("duplicate-key")
expect(intent_replay.detail).to_equal("prov-tenant-a-int-1")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_int)

step("captured webhook replays on provider_event_id (already fixed — regression fence)")
val provider = PaymentProvider(name: "mock", shared_secret: "s3cr3t")
val env_wh = envelope("py-wh")
val sig = provider_sign(provider, env_wh.payload)
expect(payment_webhook_receive(store, s, t, admin, env_wh, provider, "prov-tenant-a-int-1", "captured", sig, "evt-1", 200).reason).to_equal("accepted")
val fp_wh = effect_fingerprint(store, "tenant-a")
val wh_replay = payment_webhook_receive(store, s, t, admin, env_wh, provider, "prov-tenant-a-int-1", "captured", sig, "evt-1", 200)
expect(wh_replay.reason).to_equal("duplicate-key")
expect(wh_replay.detail).to_equal("int-1:captured")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_wh)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### hcm: hire, amend, clock in/out, leave request/decide, and terminate replay with one effect

- Hire an employee
   - Expected: hcm_hire(store, s, t, admin, envelope("hc-hire"), "emp-1", "Ann", 0, 2000, 40).reason equals `accepted`
   - Expected: hcm_hire(store, s, t, admin, envelope("hc-hire"), "emp-1", "Ann", 0, 2000, 40).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_hire`
- contract amend replays
   - Expected: hcm_contract_amend(store, s, t, admin, envelope("hc-am"), "emp-1", 100, 2500, 40).reason equals `accepted`
   - Expected: hcm_contract_amend(store, s, t, admin, envelope("hc-am"), "emp-1", 100, 2500, 40).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_am`
- clock in: the open punch it creates is its own effect
   - Expected: hcm_clock_in(store, s, t, admin, envelope("hc-ci"), "emp-1", 1000).reason equals `accepted`
   - Expected: hcm_clock_in(store, s, t, admin, envelope("hc-ci"), "emp-1", 1000).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_ci`
- clock out: the punch it closes is its own effect
   - Expected: hcm_clock_out(store, s, t, admin, envelope("hc-co"), "emp-1", 2000).reason equals `accepted`
   - Expected: hcm_clock_out(store, s, t, admin, envelope("hc-co"), "emp-1", 2000).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_co`
- leave request and decision both replay
   - Expected: hcm_leave_request(store, s, t, admin, envelope("hc-lr"), "lv-1", "emp-1", 5000, 9000, "annual").reason equals `accepted`
   - Expected: hcm_leave_request(store, s, t, admin, envelope("hc-lr"), "lv-1", "emp-1", 5000, 9000, "annual").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_lr`
   - Expected: hcm_leave_decide(store, s, t, admin, envelope("hc-ld"), "lv-1", true).reason equals `accepted`
   - Expected: hcm_leave_decide(store, s, t, admin, envelope("hc-ld"), "lv-1", true).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_ld`
- terminate replays
   - Expected: hcm_terminate(store, s, t, admin, envelope("hc-tm"), "emp-1", 99999).reason equals `accepted`
   - Expected: hcm_terminate(store, s, t, admin, envelope("hc-tm"), "emp-1", 99999).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_tm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hire an employee")
val store = fresh_store("hcm")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
hcm_setup(store)
expect(hcm_hire(store, s, t, admin, envelope("hc-hire"), "emp-1", "Ann", 0, 2000, 40).reason).to_equal("accepted")
val fp_hire = effect_fingerprint(store, "tenant-a")
expect(hcm_hire(store, s, t, admin, envelope("hc-hire"), "emp-1", "Ann", 0, 2000, 40).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_hire)

step("contract amend replays")
expect(hcm_contract_amend(store, s, t, admin, envelope("hc-am"), "emp-1", 100, 2500, 40).reason).to_equal("accepted")
val fp_am = effect_fingerprint(store, "tenant-a")
expect(hcm_contract_amend(store, s, t, admin, envelope("hc-am"), "emp-1", 100, 2500, 40).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_am)

step("clock in: the open punch it creates is its own effect")
expect(hcm_clock_in(store, s, t, admin, envelope("hc-ci"), "emp-1", 1000).reason).to_equal("accepted")
val fp_ci = effect_fingerprint(store, "tenant-a")
expect(hcm_clock_in(store, s, t, admin, envelope("hc-ci"), "emp-1", 1000).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_ci)

step("clock out: the punch it closes is its own effect")
expect(hcm_clock_out(store, s, t, admin, envelope("hc-co"), "emp-1", 2000).reason).to_equal("accepted")
val fp_co = effect_fingerprint(store, "tenant-a")
expect(hcm_clock_out(store, s, t, admin, envelope("hc-co"), "emp-1", 2000).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_co)

step("leave request and decision both replay")
expect(hcm_leave_request(store, s, t, admin, envelope("hc-lr"), "lv-1", "emp-1", 5000, 9000, "annual").reason).to_equal("accepted")
val fp_lr = effect_fingerprint(store, "tenant-a")
expect(hcm_leave_request(store, s, t, admin, envelope("hc-lr"), "lv-1", "emp-1", 5000, 9000, "annual").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_lr)
expect(hcm_leave_decide(store, s, t, admin, envelope("hc-ld"), "lv-1", true).reason).to_equal("accepted")
val fp_ld = effect_fingerprint(store, "tenant-a")
expect(hcm_leave_decide(store, s, t, admin, envelope("hc-ld"), "lv-1", true).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_ld)

step("terminate replays")
expect(hcm_terminate(store, s, t, admin, envelope("hc-tm"), "emp-1", 99999).reason).to_equal("accepted")
val fp_tm = effect_fingerprint(store, "tenant-a")
expect(hcm_terminate(store, s, t, admin, envelope("hc-tm"), "emp-1", 99999).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_tm)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### procurement: requisition, approval, PO, receipt, and invoice replay with one effect

- Register a supplier and raise a requisition
   - Expected: proc_requisition_create(store, s, t, admin, envelope("pr-req"), "req-1", "SKU-1", 5).reason equals `accepted`
   - Expected: proc_requisition_create(store, s, t, admin, envelope("pr-req"), "req-1", "SKU-1", 5).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_req`
- approve: the approved status is this command's OWN effect
   - Expected: proc_requisition_approve(store, s, t, admin, envelope("pr-app"), "req-1").reason equals `accepted`
   - Expected: app_replay.reason equals `duplicate-key`
   - Expected: app_replay.detail equals `req-1`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_app`
- PO create replays
   - Expected: proc_po_create(store, s, t, admin, envelope("pr-po"), "po-1", "req-1", "sup-1", usd(1000)).reason equals `accepted`
   - Expected: proc_po_create(store, s, t, admin, envelope("pr-po"), "po-1", "req-1", "sup-1", usd(1000)).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_po`
- receipt and invoice replay (reference shape — regression fence)
   - Expected: proc_receive(store, s, t, admin, envelope("pr-rc"), "po-1", 5).reason equals `accepted`
   - Expected: proc_receive(store, s, t, admin, envelope("pr-rc"), "po-1", 5).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_rc`
   - Expected: sale_available_stock(store, "tenant-a", "SKU-1") equals `5`
   - Expected: proc_invoice_record(store, s, t, admin, envelope("pr-inv"), "po-1", "inv-1", 5).reason equals `accepted`
   - Expected: proc_invoice_record(store, s, t, admin, envelope("pr-inv"), "po-1", "inv-1", 5).reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_inv`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register a supplier and raise a requisition")
val store = fresh_store("procurement")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_setup(store)
proc_setup(store)
proc_supplier_add(store, s, t, admin, "sup-1", "Acme Supply")
expect(proc_requisition_create(store, s, t, admin, envelope("pr-req"), "req-1", "SKU-1", 5).reason).to_equal("accepted")
val fp_req = effect_fingerprint(store, "tenant-a")
expect(proc_requisition_create(store, s, t, admin, envelope("pr-req"), "req-1", "SKU-1", 5).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_req)

step("approve: the approved status is this command's OWN effect")
expect(proc_requisition_approve(store, s, t, admin, envelope("pr-app"), "req-1").reason).to_equal("accepted")
val fp_app = effect_fingerprint(store, "tenant-a")
val app_replay = proc_requisition_approve(store, s, t, admin, envelope("pr-app"), "req-1")
expect(app_replay.reason).to_equal("duplicate-key")
expect(app_replay.detail).to_equal("req-1")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_app)

step("PO create replays")
expect(proc_po_create(store, s, t, admin, envelope("pr-po"), "po-1", "req-1", "sup-1", usd(1000)).reason).to_equal("accepted")
val fp_po = effect_fingerprint(store, "tenant-a")
expect(proc_po_create(store, s, t, admin, envelope("pr-po"), "po-1", "req-1", "sup-1", usd(1000)).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_po)

step("receipt and invoice replay (reference shape — regression fence)")
expect(proc_receive(store, s, t, admin, envelope("pr-rc"), "po-1", 5).reason).to_equal("accepted")
val fp_rc = effect_fingerprint(store, "tenant-a")
expect(proc_receive(store, s, t, admin, envelope("pr-rc"), "po-1", 5).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_rc)
expect(sale_available_stock(store, "tenant-a", "SKU-1")).to_equal(5)
expect(proc_invoice_record(store, s, t, admin, envelope("pr-inv"), "po-1", "inv-1", 5).reason).to_equal("accepted")
val fp_inv = effect_fingerprint(store, "tenant-a")
expect(proc_invoice_record(store, s, t, admin, envelope("pr-inv"), "po-1", "inv-1", 5).reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_inv)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### channel hub and outbox worker: re-import, re-ack, and re-dispatch produce no second effect

- Register a mock channel with one scripted external order
   - Expected: channel_register(store, s, t, admin, "ch-1", "mock").reason equals `accepted`
- First import creates exactly one internal order
   - Expected: run1.imported equals `1`
   - Expected: run1.duplicates equals `0`
   - Expected: channel_inbox_count(store, "tenant-a", "ch-1") equals `1`
- Re-import from cursor 0 dedupes on the external order id — no second effect
   - Expected: run2.imported equals `0`
   - Expected: channel_inbox_count(store, "tenant-a", "ch-1") equals `1`
- Ack once, then again: the second ack is a recorded duplicate-key
   - Expected: channel_ack_order(store, s, t, admin, adapter, "ch-1", "x-1").reason equals `accepted`
   - Expected: channel_ack_order(store, s, t, admin, adapter, "ch-1", "x-1").reason equals `duplicate-key`
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_ack`
- Outbox dispatch is exactly-once per row: a rerun dispatches nothing
   - Expected: d1.failed equals `0`
   - Expected: d2.attempted equals `0`
   - Expected: d2.dispatched equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register a mock channel with one scripted external order")
val store = fresh_store("channel")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_setup(store)
channel_setup(store)
outbox_worker_setup(store)
sale_add_product(store, s, t, admin, "SKU-1", "Widget", usd(2500))
sale_receive_stock(store, s, t, admin, "SKU-1", 100)
expect(channel_register(store, s, t, admin, "ch-1", "mock").reason).to_equal("accepted")
val adapter = mock_channel([ChannelOrder(external_id: "x-1", sku: "SKU-1", qty: 1)], 10)

step("First import creates exactly one internal order")
val run1 = channel_import_orders(store, s, t, admin, envelope("ch-imp"), adapter, "ch-1", 10)
expect(run1.ok).to_be(true)
expect(run1.imported).to_equal(1)
expect(run1.duplicates).to_equal(0)
expect(channel_inbox_count(store, "tenant-a", "ch-1")).to_equal(1)

step("Re-import from cursor 0 dedupes on the external order id — no second effect")
val run2 = channel_import_orders(store, s, t, admin, envelope("ch-imp"), mock_channel([ChannelOrder(external_id: "x-1", sku: "SKU-1", qty: 1)], 10), "ch-1", 10)
expect(run2.ok).to_be(true)
expect(run2.imported).to_equal(0)
expect(channel_inbox_count(store, "tenant-a", "ch-1")).to_equal(1)

step("Ack once, then again: the second ack is a recorded duplicate-key")
expect(channel_ack_order(store, s, t, admin, adapter, "ch-1", "x-1").reason).to_equal("accepted")
val fp_ack = effect_fingerprint(store, "tenant-a")
expect(channel_ack_order(store, s, t, admin, adapter, "ch-1", "x-1").reason).to_equal("duplicate-key")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_ack)

step("Outbox dispatch is exactly-once per row: a rerun dispatches nothing")
val d1 = outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1000, 50)
expect(d1.failed).to_equal(0)
val d2 = outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1000, 50)
expect(d2.attempted).to_equal(0)
expect(d2.dispatched).to_equal(0)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### guarded-command conformance — closed reason set

#### every reason returned across the suite satisfies reason_allowed

- Drive a denial from every module and collect the reasons
- The collected set is non-trivial and wholly inside the closed set
- The closed set itself is the frozen 16-reason list
   - Expected: reason_set().len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drive a denial from every module and collect the reasons")
val store = fresh_store("reasons")
val t = tenant_a()
val admin = admin_a()
val s = session_for(admin, t)
sale_setup(store)
proc_setup(store)
booking_setup(store)
restaurant_setup(store)
payment_setup(store)
hcm_setup(store)
channel_setup(store)
session_setup(store)
var dead = session_for(admin, t)
dead.active = false
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val cs = session_for(clerk, t)

var reasons: [text] = []
# goods_sale (W7-A-owned file, still contract-checked here)
reasons.push(sale_place_order(store, dead, t, admin, envelope("rz-1"), "o-1", "SKU-X", 1).reason)
reasons.push(sale_place_order(store, s, t, admin, envelope("rz-2"), "o-1", "SKU-X", 1).reason)
sale_add_product(store, s, t, admin, "SKU-1", "Widget", usd(2500))
reasons.push(sale_place_order(store, s, t, admin, envelope("rz-3"), "o-1", "SKU-1", 5).reason)
reasons.push(sale_add_product(store, s, t, admin, "SKU-1", "Widget", usd(0)).reason)
# procurement
reasons.push(proc_supplier_add(store, cs, t, clerk, "sup-x", "X").reason)
reasons.push(proc_receive(store, s, t, admin, envelope("rz-4"), "po-404", 1).reason)
# booking
booking_create_resource(store, s, t, admin, "res-1", "exclusive-unit", 1, "v1")
reasons.push(booking_hold(store, s, t, admin, envelope("rz-5"), "b-1", "res-404", 1, 2, 1, "", 0, 10).reason)
booking_hold(store, s, t, admin, envelope("rz-6"), "b-1", "res-1", 100, 200, 1, "", 50, 1000)
reasons.push(booking_hold(store, s, t, admin, envelope("rz-7"), "b-2", "res-1", 150, 250, 1, "", 50, 1000).reason)
# restaurant
reasons.push(order_add_line(store, s, t, admin, envelope("rz-8"), "sess-404", "l-1", "SKU-1", 1, "").reason)
table_open_session(store, s, t, admin, envelope("rz-9"), "sess-1", "v1", "t1", 2)
reasons.push(table_open_session(store, s, t, admin, envelope("rz-10"), "sess-2", "v1", "t1", 2).reason)
reasons.push(line_mark_served(store, s, t, admin, envelope("rz-11"), "sess-1", "l-404").reason)
order_add_line(store, s, t, admin, envelope("rz-12"), "sess-1", "l-1", "SKU-1", 1, "")
reasons.push(line_mark_served(store, s, t, admin, envelope("rz-13"), "sess-1", "l-1").reason)
reasons.push(bill_close_session(store, s, t, admin, envelope("rz-14"), "sess-1").reason)
# payment
val provider = PaymentProvider(name: "mock", shared_secret: "s3cr3t")
reasons.push(payment_webhook_receive(store, s, t, admin, envelope("rz-15"), provider, "prov-x", "captured", "bad-sig", "evt-x", 1).reason)
reasons.push(payment_create_intent(store, s, t, admin, envelope("rz-16"), "int-1", "order-404", 1).reason)
# hcm
reasons.push(hcm_clock_in(store, s, t, admin, envelope("rz-17"), "emp-404", 1).reason)
hcm_hire(store, s, t, admin, envelope("rz-18"), "emp-1", "Ann", 0, 2000, 40)
reasons.push(hcm_hire(store, s, t, admin, envelope("rz-19"), "emp-1", "Ann", 0, 2000, 40).reason)
# channel hub
channel_register(store, s, t, admin, "ch-1", "mock")
reasons.push(channel_list_product(store, s, t, admin, mock_channel_down([], 10), "ch-1", "SKU-1", usd(2500)).reason)
channel_kill(store, s, t, admin, "ch-1")
reasons.push(channel_ack_order(store, s, t, admin, mock_channel([], 10), "ch-1", "x-1").reason)
reasons.push(channel_import_orders(store, s, t, admin, envelope("rz-20"), mock_channel([], 10), "ch-1", 10).reason)
# session vertical — the generic, non-enumerating issuance denial
credential_seed(store, s, t, admin, "user-1", "sales", "salt", "secret")
reasons.push(session_issue(store, "tenant-a", "user-1", "wrong", 100, 900, "e").reason)
reasons.push(session_issue(store, "tenant-a", "user-404", "secret", 100, 900, "e").reason)
reasons.push(session_issue(store, "tenant-a", "user-1", "secret", 100, 900, "e").reason)

step("The collected set is non-trivial and wholly inside the closed set")
expect(reasons.len() > 20).to_be(true)
for r in reasons:
    expect(reason_allowed(r)).to_be(true)

step("The closed set itself is the frozen 16-reason list")
expect(reason_set().len()).to_equal(16)
expect(reason_allowed("totally-made-up")).to_be(false)
store_close(store)
```

</details>

### guarded-command conformance — tenant scoping

#### a session issued for tenant B is denied by every guarded command of tenant A

- Seed tenant A state, then attack it with a tenant-B session
- The intruder's session is valid for tenant B, but tenant A is authority
- Every one of them is invalid-session — no rung leaks past the first
   - Expected: denials.len() equals `15`
   - Expected: d equals `invalid-session`
- Tenant A's observable state is byte-identical afterwards
   - Expected: effect_fingerprint(store, "tenant-a") equals `fp_before`
   - Expected: effect_fingerprint(store, "tenant-b") equals `outbox=0;audit=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed tenant A state, then attack it with a tenant-B session")
val store = fresh_store("tenancy")
val ta = tenant_a()
val admin = admin_a()
val s = session_for(admin, ta)
sale_setup(store)
proc_setup(store)
booking_setup(store)
restaurant_setup(store)
payment_setup(store)
hcm_setup(store)
channel_setup(store)
sale_add_product(store, s, ta, admin, "SKU-1", "Widget", usd(2500))
sale_receive_stock(store, s, ta, admin, "SKU-1", 10)
booking_create_resource(store, s, ta, admin, "res-1", "exclusive-unit", 1, "v1")
table_open_session(store, s, ta, admin, envelope("tn-open"), "sess-1", "v1", "t1", 2)
hcm_hire(store, s, ta, admin, envelope("tn-hire"), "emp-1", "Ann", 0, 2000, 40)
channel_register(store, s, ta, admin, "ch-1", "mock")
val fp_before = effect_fingerprint(store, "tenant-a")

step("The intruder's session is valid for tenant B, but tenant A is authority")
val tb = tenant_b()
val intruder = ActorContext(actor_id: "intruder-1", role: "admin")
val bad = session_for(intruder, tb)

var denials: [text] = []
denials.push(sale_place_order(store, bad, ta, intruder, envelope("tn-1"), "o-x", "SKU-1", 1).reason)
denials.push(sale_add_product(store, bad, ta, intruder, "SKU-X", "X", usd(100)).reason)
denials.push(proc_supplier_add(store, bad, ta, intruder, "sup-x", "X").reason)
denials.push(proc_requisition_create(store, bad, ta, intruder, envelope("tn-2"), "req-x", "SKU-1", 1).reason)
denials.push(booking_hold(store, bad, ta, intruder, envelope("tn-3"), "b-x", "res-1", 1, 2, 1, "", 0, 10).reason)
denials.push(booking_cancel(store, bad, ta, intruder, envelope("tn-4"), "b-x").reason)
denials.push(table_open_session(store, bad, ta, intruder, envelope("tn-5"), "sess-x", "v1", "t2", 2).reason)
denials.push(order_add_line(store, bad, ta, intruder, envelope("tn-6"), "sess-1", "l-x", "SKU-1", 1, "").reason)
denials.push(bill_close_session(store, bad, ta, intruder, envelope("tn-7"), "sess-1").reason)
denials.push(payment_create_intent(store, bad, ta, intruder, envelope("tn-8"), "int-x", "o-1", 1).reason)
denials.push(hcm_clock_in(store, bad, ta, intruder, envelope("tn-9"), "emp-1", 1).reason)
denials.push(hcm_terminate(store, bad, ta, intruder, envelope("tn-10"), "emp-1", 9).reason)
denials.push(channel_register(store, bad, ta, intruder, "ch-x", "mock").reason)
denials.push(channel_ack_order(store, bad, ta, intruder, mock_channel([], 10), "ch-1", "x-1").reason)
denials.push(channel_import_orders(store, bad, ta, intruder, envelope("tn-11"), mock_channel([], 10), "ch-1", 10).reason)

step("Every one of them is invalid-session — no rung leaks past the first")
expect(denials.len()).to_equal(15)
for d in denials:
    expect(d).to_equal("invalid-session")

step("Tenant A's observable state is byte-identical afterwards")
expect(effect_fingerprint(store, "tenant-a")).to_equal(fp_before)
expect(effect_fingerprint(store, "tenant-b")).to_equal("outbox=0;audit=0")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
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

- **Plan:** `.spipe/simple_enterprise_suite/state.md`
- **Design:** `doc/07_guide/app/enterprise/guarded_command_contract.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
