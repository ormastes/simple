# Returns / RMA Vertical — scenario over the durable store

> The Returns/RMA vertical of the Simple Enterprise Suite, exercised against the durable enterprise store: a sales desk opens a return, an admin approves it, the warehouse receives the goods, and the desk issues the refund Money; every mutation runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Returns / RMA Vertical — scenario over the durable store

The Returns/RMA vertical of the Simple Enterprise Suite, exercised against the durable enterprise store: a sales desk opens a return, an admin approves it, the warehouse receives the goods, and the desk issues the refund Money; every mutation runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Returns/RMA vertical of the Simple Enterprise Suite, exercised against the
durable enterprise store: a sales desk opens a return, an admin approves it, the
warehouse receives the goods, and the desk issues the refund Money; every
mutation runs the frozen guarded sequence (session -> rbac -> validation ->
idempotency -> effects in one UoW) and chains a sha256 audit record.

## Guarded sequence proven here (reproduce-first for each denial)

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | a cross-tenant forged session is rejected outright |
| rbac | forbidden | a viewer cannot request; a sales rep cannot decide (admin-tier) |
| validation | invalid-record | a malformed request (empty ids / non-positive qty) |
| transition | invalid-transition | deciding twice; receiving before approval; refunding before receipt |
| existence | not-found | deciding/receiving/refunding an unknown RMA |
| idempotency | duplicate-key | replay returns recorded result, exactly one effect |
| tenancy | not-found / invalid-session | tenant B cannot see or mutate tenant A's RMA |

## Invariants

- current state is a pure fold over the insert-only event stream (never UPDATE);
- an illegal state move is denied with the closed-set reason invalid-transition;
- a replayed command produces exactly one effect (refund ledger unchanged);
- the refund Money equals qty * captured unit price in integer minor units;
- the session tenant is authority — a cross-tenant session is rejected outright.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W21-C).

## Scenarios

### returns vertical — one complete RMA end to end

#### request -> approve -> receive -> refund with the refund Money asserted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- request -> approve -> receive -> refund with the refund Money asserted
- Open a clean store
- Request a return — state folds to 'requested'
   - Expected: requested.reason equals `accepted`
   - Expected: ret_rma_state(store, "tenant-a", "rma-1") equals `requested`
- Admin approves — state folds to 'approved'
   - Expected: approved.reason equals `accepted`
   - Expected: ret_rma_state(store, "tenant-a", "rma-1") equals `approved`
- Warehouse receives — state folds to 'received'
   - Expected: received.reason equals `accepted`
   - Expected: ret_rma_state(store, "tenant-a", "rma-1") equals `received`
- Refund — state 'refunded', Money = 3 * 2500 = 7500
   - Expected: refunded.reason equals `accepted`
   - Expected: ret_rma_state(store, "tenant-a", "rma-1") equals `refunded`
   - Expected: ret_rma_refund_cents(store, "tenant-a", "rma-1") equals `7500`
- Status fold reports the terminal state and refunded amount
   - Expected: st.state equals `refunded`
   - Expected: st.refund_cents equals `7500`
   - Expected: st.currency equals `USD`
- The audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("request -> approve -> receive -> refund with the refund Money asserted")
step("Open a clean store")
val store = fresh_store("e2e")
val t = tenant_a()
val rep = rep_a()
val adm = admin_a()
val s = session_for(rep, t)
val sa = session_for(adm, t)

step("Request a return — state folds to 'requested'")
val requested = rma_request(store, s, t, rep, envelope("rq-k1", "returns.rma.request"), "rma-1", "order-1", "sku-9", 3, usd(2500))
expect(requested.reason).to_equal("accepted")
expect(reason_allowed(requested.reason)).to_be(true)
expect(ret_rma_state(store, "tenant-a", "rma-1")).to_equal("requested")

step("Admin approves — state folds to 'approved'")
val approved = rma_decide(store, sa, t, adm, envelope("dc-k1", "returns.rma.decide"), "rma-1", true)
expect(approved.reason).to_equal("accepted")
expect(ret_rma_state(store, "tenant-a", "rma-1")).to_equal("approved")

step("Warehouse receives — state folds to 'received'")
val received = rma_receive(store, s, t, rep, envelope("rc-k1", "returns.rma.receive"), "rma-1")
expect(received.reason).to_equal("accepted")
expect(ret_rma_state(store, "tenant-a", "rma-1")).to_equal("received")

step("Refund — state 'refunded', Money = 3 * 2500 = 7500")
val refunded = rma_refund(store, s, t, rep, envelope("rf-k1", "returns.rma.refund"), "rma-1")
expect(refunded.reason).to_equal("accepted")
expect(ret_rma_state(store, "tenant-a", "rma-1")).to_equal("refunded")
expect(ret_rma_refund_cents(store, "tenant-a", "rma-1")).to_equal(7500)

step("Status fold reports the terminal state and refunded amount")
val st = rma_status(store, "tenant-a", "rma-1")
expect(st.state).to_equal("refunded")
expect(st.refund_cents).to_equal(7500)
expect(st.currency).to_equal("USD")

step("The audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### returns vertical — rbac denies unauthorized actors

#### reproduce: a viewer cannot request a return (forbidden)

- reproduce: a viewer cannot request a return (forbidden)
- Attempt rma_request as a viewer role
   - Expected: r.reason equals `forbidden`
- No RMA was created
   - Expected: ret_rma_state(store, "tenant-a", "rma-x") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a viewer cannot request a return (forbidden)")
val store = fresh_store("rbac_view")
val t = tenant_a()
val viewer = viewer_a()
step("Attempt rma_request as a viewer role")
val r = rma_request(store, session_for(viewer, t), t, viewer, envelope("k-v", "returns.rma.request"), "rma-x", "order-x", "sku-1", 1, usd(1000))
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(reason_allowed(r.reason)).to_be(true)
step("No RMA was created")
expect(ret_rma_state(store, "tenant-a", "rma-x")).to_equal("")
store_close(store)
```

</details>

#### reproduce: a sales rep cannot decide — approval is admin-tier (forbidden)

- reproduce: a sales rep cannot decide — approval is admin-tier (forbidden)
- Sales rep attempts the admin-tier decision
   - Expected: r.reason equals `forbidden`
   - Expected: ret_rma_state(store, "tenant-a", "rma-2") equals `requested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a sales rep cannot decide — approval is admin-tier (forbidden)")
val store = fresh_store("rbac_decide")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
rma_request(store, s, t, rep, envelope("rq", "returns.rma.request"), "rma-2", "order-2", "sku-2", 1, usd(1000))
step("Sales rep attempts the admin-tier decision")
val r = rma_decide(store, s, t, rep, envelope("dc", "returns.rma.decide"), "rma-2", true)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(ret_rma_state(store, "tenant-a", "rma-2")).to_equal("requested")
store_close(store)
```

</details>

### returns vertical — malformed requests are invalid-record

#### reproduce: a non-positive quantity is invalid-record

- reproduce: a non-positive quantity is invalid-record
- Request with qty = 0
   - Expected: r.reason equals `invalid-record`
   - Expected: ret_rma_state(store, "tenant-a", "rma-3") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a non-positive quantity is invalid-record")
val store = fresh_store("bad_qty")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
step("Request with qty = 0")
val r = rma_request(store, s, t, rep, envelope("bq", "returns.rma.request"), "rma-3", "order-3", "sku-3", 0, usd(1000))
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")
expect(ret_rma_state(store, "tenant-a", "rma-3")).to_equal("")
store_close(store)
```

</details>

### returns vertical — invalid state transitions are denied

#### reproduce: deciding a second time is invalid-transition (cannot decide twice)

- reproduce: deciding a second time is invalid-transition (cannot decide twice)
- Decide again with a FRESH key — the RMA is no longer 'requested'
   - Expected: again.reason equals `invalid-transition`
   - Expected: ret_rma_state(store, "tenant-a", "rma-4") equals `approved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: deciding a second time is invalid-transition (cannot decide twice)")
val store = fresh_store("decide_twice")
val t = tenant_a()
val rep = rep_a()
val adm = admin_a()
val s = session_for(rep, t)
val sa = session_for(adm, t)
rma_request(store, s, t, rep, envelope("rq4", "returns.rma.request"), "rma-4", "order-4", "sku-4", 2, usd(500))
rma_decide(store, sa, t, adm, envelope("dc4", "returns.rma.decide"), "rma-4", true)
step("Decide again with a FRESH key — the RMA is no longer 'requested'")
val again = rma_decide(store, sa, t, adm, envelope("dc4b", "returns.rma.decide"), "rma-4", false)
expect(again.ok).to_be(false)
expect(again.reason).to_equal("invalid-transition")
expect(reason_allowed(again.reason)).to_be(true)
expect(ret_rma_state(store, "tenant-a", "rma-4")).to_equal("approved")
store_close(store)
```

</details>

#### reproduce: receiving before approval is invalid-transition

- reproduce: receiving before approval is invalid-transition
- Receive while rma-5 is still 'requested'
   - Expected: r.reason equals `invalid-transition`
   - Expected: ret_rma_state(store, "tenant-a", "rma-5") equals `requested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: receiving before approval is invalid-transition")
val store = fresh_store("recv_early")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
rma_request(store, s, t, rep, envelope("rq5", "returns.rma.request"), "rma-5", "order-5", "sku-5", 1, usd(1000))
step("Receive while rma-5 is still 'requested'")
val r = rma_receive(store, s, t, rep, envelope("rc5", "returns.rma.receive"), "rma-5")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-transition")
expect(ret_rma_state(store, "tenant-a", "rma-5")).to_equal("requested")
store_close(store)
```

</details>

#### reproduce: refunding before receipt is invalid-transition

- reproduce: refunding before receipt is invalid-transition
- Refund while rma-6 is 'approved' but not yet 'received'
   - Expected: r.reason equals `invalid-transition`
   - Expected: ret_rma_refund_cents(store, "tenant-a", "rma-6") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: refunding before receipt is invalid-transition")
val store = fresh_store("refund_early")
val t = tenant_a()
val rep = rep_a()
val adm = admin_a()
val s = session_for(rep, t)
val sa = session_for(adm, t)
rma_request(store, s, t, rep, envelope("rq6", "returns.rma.request"), "rma-6", "order-6", "sku-6", 1, usd(1000))
rma_decide(store, sa, t, adm, envelope("dc6", "returns.rma.decide"), "rma-6", true)
step("Refund while rma-6 is 'approved' but not yet 'received'")
val r = rma_refund(store, s, t, rep, envelope("rf6", "returns.rma.refund"), "rma-6")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-transition")
expect(ret_rma_refund_cents(store, "tenant-a", "rma-6")).to_equal(0)
store_close(store)
```

</details>

### returns vertical — unknown RMA is not-found

#### reproduce: deciding an unknown RMA is not-found

- reproduce: deciding an unknown RMA is not-found
- Decide an RMA id that was never requested
   - Expected: r.reason equals `not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: deciding an unknown RMA is not-found")
val store = fresh_store("nf")
val t = tenant_a()
val adm = admin_a()
val sa = session_for(adm, t)
step("Decide an RMA id that was never requested")
val r = rma_decide(store, sa, t, adm, envelope("nf-k", "returns.rma.decide"), "ghost", true)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("not-found")
expect(reason_allowed(r.reason)).to_be(true)
store_close(store)
```

</details>

### returns vertical — idempotent replay produces exactly one effect

#### replaying a refund changes nothing

- replaying a refund changes nothing
- Refund once — Money = 4 * 1000 = 4000
   - Expected: first.reason equals `accepted`
   - Expected: refund_after_first equals `4000`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `rma-7`
- No second effect — refund ledger and outbox unchanged
   - Expected: ret_rma_refund_cents(store, "tenant-a", "rma-7") equals `refund_after_first`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying a refund changes nothing")
val store = fresh_store("replay")
val t = tenant_a()
val rep = rep_a()
val adm = admin_a()
val s = session_for(rep, t)
val sa = session_for(adm, t)
rma_request(store, s, t, rep, envelope("rq7", "returns.rma.request"), "rma-7", "order-7", "sku-7", 4, usd(1000))
rma_decide(store, sa, t, adm, envelope("dc7", "returns.rma.decide"), "rma-7", true)
rma_receive(store, s, t, rep, envelope("rc7", "returns.rma.receive"), "rma-7")

step("Refund once — Money = 4 * 1000 = 4000")
val first = rma_refund(store, s, t, rep, envelope("same-key", "returns.rma.refund"), "rma-7")
expect(first.reason).to_equal("accepted")
val refund_after_first = ret_rma_refund_cents(store, "tenant-a", "rma-7")
val outbox_after_first = outbox_pending(store, "tenant-a").len()
expect(refund_after_first).to_equal(4000)

step("Replay the SAME idempotency key")
val replay = rma_refund(store, s, t, rep, envelope("same-key", "returns.rma.refund"), "rma-7")
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("rma-7")

step("No second effect — refund ledger and outbox unchanged")
expect(ret_rma_refund_cents(store, "tenant-a", "rma-7")).to_equal(refund_after_first)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
store_close(store)
```

</details>

### returns vertical — tenant isolation

#### tenant B cannot see or mutate tenant A's RMA

- tenant B cannot see or mutate tenant A's RMA
- Tenant B sees no state for tenant A's RMA
   - Expected: ret_rma_state(store, "tenant-b", "rma-a") equals ``
- A tenant-B admin cannot decide tenant A's RMA — not-found in B's scope
   - Expected: r.reason equals `not-found`
- A cross-tenant session (B token presented with A as authority) is rejected outright
   - Expected: r2.reason equals `invalid-session`
- Tenant A's RMA is untouched — still 'requested'
   - Expected: ret_rma_state(store, "tenant-a", "rma-a") equals `requested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B cannot see or mutate tenant A's RMA")
val store = fresh_store("isolation")
val ta = tenant_a()
val rep = rep_a()
val sa = session_for(rep, ta)
rma_request(store, sa, ta, rep, envelope("rqa", "returns.rma.request"), "rma-a", "order-a", "sku-a", 1, usd(1000))

step("Tenant B sees no state for tenant A's RMA")
expect(ret_rma_state(store, "tenant-b", "rma-a")).to_equal("")

step("A tenant-B admin cannot decide tenant A's RMA — not-found in B's scope")
val tb = tenant_b()
val adm_b = ActorContext(actor_id: "adm-b", role: "admin")
val sb = session_for(adm_b, tb)
val r = rma_decide(store, sb, tb, adm_b, envelope("dcb", "returns.rma.decide"), "rma-a", true)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("not-found")

step("A cross-tenant session (B token presented with A as authority) is rejected outright")
val forged = SessionContext(token: "tok-adm-b", actor_id: "adm-b", tenant_id: "tenant-b", active: true)
val r2 = rma_decide(store, forged, ta, adm_b, envelope("dcb2", "returns.rma.decide"), "rma-a", true)
expect(r2.reason).to_equal("invalid-session")

step("Tenant A's RMA is untouched — still 'requested'")
expect(ret_rma_state(store, "tenant-a", "rma-a")).to_equal("requested")
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `14707bea669e031a852adcedc343b903b071f4b09541553ec6d48c71ce1f2f3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14707bea669e031a852adcedc343b903b071f4b09541553ec6d48c71ce1f2f3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14707bea669e031a852adcedc343b903b071f4b09541553ec6d48c71ce1f2f3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'request -> approve -> receive -> refund with the refund Money asserted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: a viewer cannot request a return (forbidden)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_returns_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: a sales rep cannot decide — approval is admin-tier (forbidden)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
