# Inventory / Stock-Control Vertical — receive, reserve, adjust

> The stock-control flow of the Simple Enterprise Suite (lane W18-A) against the durable enterprise store: goods are received into a (SKU, location), reserved against available stock, and corrected by audited adjustments. On-hand and available are pure-Simple folds over an insert-only signed movement ledger (`inv_moves`) — never an UPDATE.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inventory / Stock-Control Vertical — receive, reserve, adjust

The stock-control flow of the Simple Enterprise Suite (lane W18-A) against the durable enterprise store: goods are received into a (SKU, location), reserved against available stock, and corrected by audited adjustments. On-hand and available are pure-Simple folds over an insert-only signed movement ledger (`inv_moves`) — never an UPDATE.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md (W18-A) |
| Design | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The stock-control flow of the Simple Enterprise Suite (lane W18-A) against
the durable enterprise store: goods are received into a (SKU, location),
reserved against available stock, and corrected by audited adjustments.
On-hand and available are pure-Simple folds over an insert-only signed
movement ledger (`inv_moves`) — never an UPDATE.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | cross-tenant / inactive session rejected |
| rbac | forbidden | sales role cannot receive stock |
| validation | insufficient-stock | reserve beyond available; adjust below reserved |
| idempotency | duplicate-key | replay returns recorded result, one effect |

## Invariants

- available = on_hand − reserved; a reservation lowers available, not on_hand.
- every mutation appends a sha256-chained audit row (verified end to end).
- tenant B sees none of tenant A's stock and cannot mutate it.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md (W18-A)
**Design:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W18-A).

## Scenarios

### inventory vertical — receive, reserve, and on-hand math

#### receives stock, reserves against available, and derives correct quantities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- receives stock, reserves against available, and derives correct quantities
- Open a clean store and receive 10 units of SKU-1 into L1
   - Expected: stock_receive(store, sk, t, keeper, envelope("e2e-rc", "proc.po.receive"), "SKU-1", "L1", 10).reason equals `accepted`
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`
   - Expected: stock_available(store, "tenant-a", "SKU-1", "L1") equals `10`
- Reserve 4 units — available falls to 6, on-hand stays 10
   - Expected: stock_reserve(store, sk, t, keeper, envelope("e2e-rsv", "proc.po.receive"), "SKU-1", "L1", 4).reason equals `accepted`
   - Expected: stock_reserved(store, "tenant-a", "SKU-1", "L1") equals `4`
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`
   - Expected: stock_available(store, "tenant-a", "SKU-1", "L1") equals `6`
- Admin adjusts +2 (found stock) — on-hand 12, available 8
   - Expected: stock_adjust(store, sa, t, admin, envelope("e2e-adj", "inventory.stock.adjust"), "SKU-1", "L1", 2).reason equals `accepted`
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L1") equals `12`
   - Expected: stock_available(store, "tenant-a", "SKU-1", "L1") equals `8`
- A different location is independent (no cross-location bleed)
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L2") equals `0`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("receives stock, reserves against available, and derives correct quantities")
step("Open a clean store and receive 10 units of SKU-1 into L1")
val store = fresh_store("e2e")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
expect(stock_receive(store, sk, t, keeper, envelope("e2e-rc", "proc.po.receive"), "SKU-1", "L1", 10).reason).to_equal("accepted")
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
expect(stock_available(store, "tenant-a", "SKU-1", "L1")).to_equal(10)

step("Reserve 4 units — available falls to 6, on-hand stays 10")
expect(stock_reserve(store, sk, t, keeper, envelope("e2e-rsv", "proc.po.receive"), "SKU-1", "L1", 4).reason).to_equal("accepted")
expect(stock_reserved(store, "tenant-a", "SKU-1", "L1")).to_equal(4)
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
expect(stock_available(store, "tenant-a", "SKU-1", "L1")).to_equal(6)

step("Admin adjusts +2 (found stock) — on-hand 12, available 8")
val admin = admin_a()
val sa = session_for(admin, t)
expect(stock_adjust(store, sa, t, admin, envelope("e2e-adj", "inventory.stock.adjust"), "SKU-1", "L1", 2).reason).to_equal("accepted")
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(12)
expect(stock_available(store, "tenant-a", "SKU-1", "L1")).to_equal(8)

step("A different location is independent (no cross-location bleed)")
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L2")).to_equal(0)

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### inventory vertical — guarded denials (reproduce-first)

#### denies an unauthorized actor at the rbac rung

- denies an unauthorized actor at the rbac rung
- A sales-role actor attempts a receipt — the rbac rung fires 'forbidden'
   - Expected: r.reason equals `forbidden`
- Adjust is admin-only: even the procurement keeper is denied
   - Expected: stock_adjust(store, session_for(keeper, t), t, keeper, envelope("rbac-adj", "inventory.stock.adjust"), "SKU-1", "L1", -1).reason equals `forbidden`
- An inactive session is rejected before rbac
   - Expected: stock_receive(store, dead, t, keeper, envelope("rbac-dead", "proc.po.receive"), "SKU-1", "L1", 1).reason equals `invalid-session`
- The ledger is untouched by every denial
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an unauthorized actor at the rbac rung")
val store = seed_received("rbac")
val t = tenant_a()
step("A sales-role actor attempts a receipt — the rbac rung fires 'forbidden'")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val r = stock_receive(store, session_for(clerk, t), t, clerk, envelope("rbac-rc", "proc.po.receive"), "SKU-1", "L1", 5)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
step("Adjust is admin-only: even the procurement keeper is denied")
val keeper = keeper_a()
expect(stock_adjust(store, session_for(keeper, t), t, keeper, envelope("rbac-adj", "inventory.stock.adjust"), "SKU-1", "L1", -1).reason).to_equal("forbidden")
step("An inactive session is rejected before rbac")
var dead = session_for(keeper, t)
dead.active = false
expect(stock_receive(store, dead, t, keeper, envelope("rbac-dead", "proc.po.receive"), "SKU-1", "L1", 1).reason).to_equal("invalid-session")
step("The ledger is untouched by every denial")
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
store_close(store)
```

</details>

#### denies an over-reservation with the closed-set reason and no effect

- denies an over-reservation with the closed-set reason and no effect
- Reserve 7 of the 10 available — accepted, available now 3
   - Expected: stock_reserve(store, sk, t, keeper, envelope("or-1", "proc.po.receive"), "SKU-1", "L1", 7).reason equals `accepted`
   - Expected: stock_available(store, "tenant-a", "SKU-1", "L1") equals `3`
- Attempt to reserve 5 more — only 3 available, must be denied
   - Expected: r.reason equals `insufficient-stock`
   - Expected: r.detail equals `over-reserve:SKU-1@L1:available=3:got=5`
- No effect — reserved and available unchanged
   - Expected: stock_reserved(store, "tenant-a", "SKU-1", "L1") equals `7`
   - Expected: stock_available(store, "tenant-a", "SKU-1", "L1") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an over-reservation with the closed-set reason and no effect")
val store = seed_received("overreserve")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
step("Reserve 7 of the 10 available — accepted, available now 3")
expect(stock_reserve(store, sk, t, keeper, envelope("or-1", "proc.po.receive"), "SKU-1", "L1", 7).reason).to_equal("accepted")
expect(stock_available(store, "tenant-a", "SKU-1", "L1")).to_equal(3)
step("Attempt to reserve 5 more — only 3 available, must be denied")
val r = stock_reserve(store, sk, t, keeper, envelope("or-2", "proc.po.receive"), "SKU-1", "L1", 5)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("insufficient-stock")
expect(r.detail).to_equal("over-reserve:SKU-1@L1:available=3:got=5")
step("No effect — reserved and available unchanged")
expect(stock_reserved(store, "tenant-a", "SKU-1", "L1")).to_equal(7)
expect(stock_available(store, "tenant-a", "SKU-1", "L1")).to_equal(3)
store_close(store)
```

</details>

### inventory vertical — idempotent replay produces exactly one effect

#### replaying the same receive command changes nothing

- replaying the same receive command changes nothing
- Receive once with a fixed key
   - Expected: stock_receive(store, sk, t, keeper, envelope("same-key", "proc.po.receive"), "SKU-1", "L1", 3).reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `SKU-1@L1`
- No second effect — on-hand and outbox unchanged
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L1") equals `on_hand_after`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying the same receive command changes nothing")
val store = seed_received("replay")
val t = tenant_a()
val keeper = keeper_a()
val sk = session_for(keeper, t)
step("Receive once with a fixed key")
expect(stock_receive(store, sk, t, keeper, envelope("same-key", "proc.po.receive"), "SKU-1", "L1", 3).reason).to_equal("accepted")
val on_hand_after = stock_on_hand(store, "tenant-a", "SKU-1", "L1")
val outbox_after = outbox_pending(store, "tenant-a").len()
step("Replay the SAME idempotency key")
val replay = stock_receive(store, sk, t, keeper, envelope("same-key", "proc.po.receive"), "SKU-1", "L1", 3)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("SKU-1@L1")
step("No second effect — on-hand and outbox unchanged")
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(on_hand_after)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after)
store_close(store)
```

</details>

### inventory vertical — tenant isolation

#### tenant B sees none of tenant A's stock and cannot mutate it

- tenant B sees none of tenant A's stock and cannot mutate it
- Tenant B sees zero on-hand and zero available for the same SKU/location
   - Expected: stock_on_hand(store, "tenant-b", "SKU-1", "L1") equals `0`
   - Expected: stock_available(store, "tenant-b", "SKU-1", "L1") equals `0`
- A tenant-B keeper reserving against tenant A's stock is denied (its own available is 0)
   - Expected: stock_reserve(store, sbb, tb, keeper_b, envelope("iso-rsv", "proc.po.receive"), "SKU-1", "L1", 1).reason equals `insufficient-stock`
- A cross-tenant session (tenant-B session against tenant-A context) is rejected outright
   - Expected: stock_receive(store, sbb, ta, keeper_b, envelope("iso-rc", "proc.po.receive"), "SKU-1", "L1", 1).reason equals `invalid-session`
- Tenant A's ledger is untouched
   - Expected: stock_on_hand(store, "tenant-a", "SKU-1", "L1") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B sees none of tenant A's stock and cannot mutate it")
val store = seed_received("isolation")
step("Tenant B sees zero on-hand and zero available for the same SKU/location")
expect(stock_on_hand(store, "tenant-b", "SKU-1", "L1")).to_equal(0)
expect(stock_available(store, "tenant-b", "SKU-1", "L1")).to_equal(0)
step("A tenant-B keeper reserving against tenant A's stock is denied (its own available is 0)")
val tb = tenant_b()
val keeper_b = ActorContext(actor_id: "keeper-b", role: "procurement")
val sbb = session_for(keeper_b, tb)
expect(stock_reserve(store, sbb, tb, keeper_b, envelope("iso-rsv", "proc.po.receive"), "SKU-1", "L1", 1).reason).to_equal("insufficient-stock")
step("A cross-tenant session (tenant-B session against tenant-A context) is rejected outright")
val ta = tenant_a()
expect(stock_receive(store, sbb, ta, keeper_b, envelope("iso-rc", "proc.po.receive"), "SKU-1", "L1", 1).reason).to_equal("invalid-session")
step("Tenant A's ledger is untouched")
expect(stock_on_hand(store, "tenant-a", "SKU-1", "L1")).to_equal(10)
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

- **Plan:** `.spipe/simple_enterprise_suite/state.md (W18-A)`
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

- Canonical SPipe generation for source `f22d46405958bad5de183080f4d3d3ebe939b16f9509603c9be573aa80ab9112`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f22d46405958bad5de183080f4d3d3ebe939b16f9509603c9be573aa80ab9112`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f22d46405958bad5de183080f4d3d3ebe939b16f9509603c9be573aa80ab9112`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'receives stock, reserves against available, and derives correct quantities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies an unauthorized actor at the rbac rung' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_inventory_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies an over-reservation with the closed-set reason and no effect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
