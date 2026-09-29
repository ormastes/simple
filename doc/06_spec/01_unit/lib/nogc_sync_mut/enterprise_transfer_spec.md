# Inter-Location Stock Transfers — dispatch, receive, conservation

> The stock-transfer flow of the Simple Enterprise Suite (lane W22-C) against the durable enterprise store: stock is seeded into a location, then moved between locations as a two-phase event log — dispatch decrements the SOURCE and marks in-transit, receive increments the DESTINATION and marks received. Per-location on-hand is a pure-Simple fold over an insert-only signed movement ledger (`xfer_moves`) — never an UPDATE.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inter-Location Stock Transfers — dispatch, receive, conservation

The stock-transfer flow of the Simple Enterprise Suite (lane W22-C) against the durable enterprise store: stock is seeded into a location, then moved between locations as a two-phase event log — dispatch decrements the SOURCE and marks in-transit, receive increments the DESTINATION and marks received. Per-location on-hand is a pure-Simple fold over an insert-only signed movement ledger (`xfer_moves`) — never an UPDATE.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md (W22-C) |
| Design | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The stock-transfer flow of the Simple Enterprise Suite (lane W22-C) against the
durable enterprise store: stock is seeded into a location, then moved between
locations as a two-phase event log — dispatch decrements the SOURCE and marks
in-transit, receive increments the DESTINATION and marks received. Per-location
on-hand is a pure-Simple fold over an insert-only signed movement ledger
(`xfer_moves`) — never an UPDATE.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | cross-tenant / inactive session rejected |
| rbac | forbidden | sales role cannot dispatch |
| validation | insufficient-stock | dispatch more than source on-hand |
| transition | invalid-transition | receive before dispatch; double-receive |
| idempotency | duplicate-key | replay returns recorded result, one effect |

## Invariants

- source decremented at dispatch; destination incremented only at receive.
- a completed transfer conserves total on-hand across all locations.
- tenant B sees none of tenant A's stock and cannot mutate it.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md (W22-C)
**Design:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W22-C).

## Scenarios

### transfer vertical — two-phase dispatch and receive

#### dispatch decrements source, receive increments destination, total conserved

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatch decrements source, receive increments destination, total conserved
- Seed 10 units of SKU-1 into L1
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `0`
- Dispatch 4 units L1 -> L2 — source falls to 6, destination stays 0 (in transit)
   - Expected: transfer_dispatch(store, sk, t, keeper, envelope("e2e-dsp", "transfer.stock.dispatch"), "TR-1", "SKU-1", 4, "L1", "L2").reason equals `accepted`
   - Expected: transfer_status(store, "tenant-a", "TR-1") equals `in-transit`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `6`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `0`
- Mid-flight the grand total dips by the in-transit quantity (6, not 10)
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") + location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `6`
- Receive TR-1 — destination rises to 4, transfer received
   - Expected: transfer_receive(store, sk, t, keeper, envelope("e2e-rcv", "transfer.stock.receive"), "TR-1").reason equals `accepted`
   - Expected: transfer_status(store, "tenant-a", "TR-1") equals `received`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `6`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `4`
- Conservation: a completed transfer leaves the grand total unchanged at 10
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") + location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `10`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatch decrements source, receive increments destination, total conserved")
step("Seed 10 units of SKU-1 into L1")
val store = seed_l1("e2e")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
expect(location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(0)

step("Dispatch 4 units L1 -> L2 — source falls to 6, destination stays 0 (in transit)")
expect(transfer_dispatch(store, sk, t, keeper, envelope("e2e-dsp", "transfer.stock.dispatch"), "TR-1", "SKU-1", 4, "L1", "L2").reason).to_equal("accepted")
expect(transfer_status(store, "tenant-a", "TR-1")).to_equal("in-transit")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(6)
expect(location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(0)
step("Mid-flight the grand total dips by the in-transit quantity (6, not 10)")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1") + location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(6)

step("Receive TR-1 — destination rises to 4, transfer received")
expect(transfer_receive(store, sk, t, keeper, envelope("e2e-rcv", "transfer.stock.receive"), "TR-1").reason).to_equal("accepted")
expect(transfer_status(store, "tenant-a", "TR-1")).to_equal("received")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(6)
expect(location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(4)
step("Conservation: a completed transfer leaves the grand total unchanged at 10")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1") + location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(10)

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### transfer vertical — over-transfer denied (reproduce-first)

#### denies dispatching more than the source location's on-hand with exact numbers and no effect

- denies dispatching more than the source location's on-hand with exact numbers and no effect
- Attempt to dispatch 15 of the 10 on-hand from L1 — must be denied
   - Expected: r.reason equals `insufficient-stock`
   - Expected: r.detail equals `over-transfer:TR-OV:SKU-1@L1:on_hand=10:got=15`
- No effect — L1 on-hand unchanged, no transfer created
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`
   - Expected: transfer_status(store, "tenant-a", "TR-OV") equals ``
   - Expected: transfer_route(store, "tenant-a", "TR-OV").1 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies dispatching more than the source location's on-hand with exact numbers and no effect")
val store = seed_l1("over")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
step("Attempt to dispatch 15 of the 10 on-hand from L1 — must be denied")
val r = transfer_dispatch(store, sk, t, keeper, envelope("ov-1", "transfer.stock.dispatch"), "TR-OV", "SKU-1", 15, "L1", "L2")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("insufficient-stock")
expect(r.detail).to_equal("over-transfer:TR-OV:SKU-1@L1:on_hand=10:got=15")
step("No effect — L1 on-hand unchanged, no transfer created")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
expect(transfer_status(store, "tenant-a", "TR-OV")).to_equal("")
expect(transfer_route(store, "tenant-a", "TR-OV").1).to_equal(-1)
store_close(store)
```

</details>

### transfer vertical — illegal transitions denied

#### receiving before dispatch and receiving twice are both invalid-transition

- receiving before dispatch and receiving twice are both invalid-transition
- Receive an unknown/never-dispatched transfer — invalid-transition, no effect
   - Expected: early.reason equals `invalid-transition`
   - Expected: early.detail equals `TR-2:`
- Dispatch then receive TR-2 legitimately
   - Expected: transfer_dispatch(store, sk, t, keeper, envelope("tr-dsp", "transfer.stock.dispatch"), "TR-2", "SKU-1", 3, "L1", "L2").reason equals `accepted`
   - Expected: transfer_receive(store, sk, t, keeper, envelope("tr-rcv", "transfer.stock.receive"), "TR-2").reason equals `accepted`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `3`
- Receive TR-2 a SECOND time with a fresh key — invalid-transition (already received), no effect
   - Expected: again.reason equals `invalid-transition`
   - Expected: again.detail equals `TR-2:received`
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L2") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("receiving before dispatch and receiving twice are both invalid-transition")
val store = seed_l1("trans")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
step("Receive an unknown/never-dispatched transfer — invalid-transition, no effect")
val early = transfer_receive(store, sk, t, keeper, envelope("tr-early", "transfer.stock.receive"), "TR-2")
expect(early.ok).to_be(false)
expect(early.reason).to_equal("invalid-transition")
expect(early.detail).to_equal("TR-2:")

step("Dispatch then receive TR-2 legitimately")
expect(transfer_dispatch(store, sk, t, keeper, envelope("tr-dsp", "transfer.stock.dispatch"), "TR-2", "SKU-1", 3, "L1", "L2").reason).to_equal("accepted")
expect(transfer_receive(store, sk, t, keeper, envelope("tr-rcv", "transfer.stock.receive"), "TR-2").reason).to_equal("accepted")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(3)

step("Receive TR-2 a SECOND time with a fresh key — invalid-transition (already received), no effect")
val again = transfer_receive(store, sk, t, keeper, envelope("tr-rcv2", "transfer.stock.receive"), "TR-2")
expect(again.ok).to_be(false)
expect(again.reason).to_equal("invalid-transition")
expect(again.detail).to_equal("TR-2:received")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(3)
store_close(store)
```

</details>

### transfer vertical — guarded denials

#### denies an unauthorized actor and an inactive session before any effect

- denies an unauthorized actor and an inactive session before any effect
- A sales-role actor attempts a dispatch — the rbac rung fires 'forbidden'
   - Expected: r.reason equals `forbidden`
- An inactive session is rejected before rbac
   - Expected: transfer_dispatch(store, dead, t, keeper, envelope("rb-dead", "transfer.stock.dispatch"), "TR-4", "SKU-1", 1, "L1", "L2").reason equals `invalid-session`
- The ledger is untouched by every denial
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an unauthorized actor and an inactive session before any effect")
val store = seed_l1("rbac")
val t = tenant_a()
step("A sales-role actor attempts a dispatch — the rbac rung fires 'forbidden'")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val r = transfer_dispatch(store, session_for(clerk, t), t, clerk, envelope("rb-dsp", "transfer.stock.dispatch"), "TR-3", "SKU-1", 2, "L1", "L2")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
step("An inactive session is rejected before rbac")
val keeper = keeper_a()
var dead = session_for(keeper, t)
dead.active = false
expect(transfer_dispatch(store, dead, t, keeper, envelope("rb-dead", "transfer.stock.dispatch"), "TR-4", "SKU-1", 1, "L1", "L2").reason).to_equal("invalid-session")
step("The ledger is untouched by every denial")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
store_close(store)
```

</details>

### transfer vertical — idempotent replay produces exactly one effect

#### replaying the same dispatch command changes nothing

- replaying the same dispatch command changes nothing
- Dispatch once with a fixed key
   - Expected: transfer_dispatch(store, sk, t, keeper, envelope("same-key", "transfer.stock.dispatch"), "TR-5", "SKU-1", 4, "L1", "L2").reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `TR-5`
- No second effect — source on-hand and outbox unchanged
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `src_after`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying the same dispatch command changes nothing")
val store = seed_l1("replay")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
step("Dispatch once with a fixed key")
expect(transfer_dispatch(store, sk, t, keeper, envelope("same-key", "transfer.stock.dispatch"), "TR-5", "SKU-1", 4, "L1", "L2").reason).to_equal("accepted")
val src_after = location_on_hand(store, "tenant-a", "SKU-1", "L1")
val outbox_after = outbox_pending(store, "tenant-a").len()
step("Replay the SAME idempotency key")
val replay = transfer_dispatch(store, sk, t, keeper, envelope("same-key", "transfer.stock.dispatch"), "TR-5", "SKU-1", 4, "L1", "L2")
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("TR-5")
step("No second effect — source on-hand and outbox unchanged")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(src_after)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after)
store_close(store)
```

</details>

### transfer vertical — tenant isolation

#### tenant B sees none of tenant A's stock and cannot move it

- tenant B sees none of tenant A's stock and cannot move it
- Tenant B sees zero on-hand for the same SKU/location
   - Expected: location_on_hand(store, "tenant-b", "SKU-1", "L1") equals `0`
- A tenant-B keeper dispatching against tenant A's stock is denied (its own on-hand is 0)
   - Expected: transfer_dispatch(store, sbb, tb, keeper_b, envelope("iso-dsp", "transfer.stock.dispatch"), "TR-B", "SKU-1", 1, "L1", "L2").reason equals `insufficient-stock`
- A cross-tenant session (tenant-B session against tenant-A context) is rejected outright
   - Expected: transfer_dispatch(store, sbb, ta, keeper_b, envelope("iso-x", "transfer.stock.dispatch"), "TR-X", "SKU-1", 1, "L1", "L2").reason equals `invalid-session`
- Tenant A's ledger is untouched
   - Expected: location_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B sees none of tenant A's stock and cannot move it")
val store = seed_l1("iso")
step("Tenant B sees zero on-hand for the same SKU/location")
expect(location_on_hand(store, "tenant-b", "SKU-1", "L1")).to_equal(0)
step("A tenant-B keeper dispatching against tenant A's stock is denied (its own on-hand is 0)")
val tb = tenant_b()
val keeper_b = ActorContext(actor_id: "keeper-b", role: "procurement")
val sbb = session_for(keeper_b, tb)
expect(transfer_dispatch(store, sbb, tb, keeper_b, envelope("iso-dsp", "transfer.stock.dispatch"), "TR-B", "SKU-1", 1, "L1", "L2").reason).to_equal("insufficient-stock")
step("A cross-tenant session (tenant-B session against tenant-A context) is rejected outright")
val ta = tenant_a()
expect(transfer_dispatch(store, sbb, ta, keeper_b, envelope("iso-x", "transfer.stock.dispatch"), "TR-X", "SKU-1", 1, "L1", "L2").reason).to_equal("invalid-session")
step("Tenant A's ledger is untouched")
expect(location_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `.spipe/simple_enterprise_suite/state.md (W22-C)`
- **Design:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e76b0eb74a2e3593794d795d38532c07c3bafb97d7e9a0cd04763bdec9622970`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e76b0eb74a2e3593794d795d38532c07c3bafb97d7e9a0cd04763bdec9622970`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e76b0eb74a2e3593794d795d38532c07c3bafb97d7e9a0cd04763bdec9622970`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatch decrements source, receive increments destination, total conserved' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies dispatching more than the source location's on-hand with exact numbers and no effect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_transfer_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'receiving before dispatch and receiving twice are both invalid-transition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
