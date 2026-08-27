# Manufacturing / Bill-of-Materials Vertical — define BOM, release + complete WOs

> The manufacturing flow of the Simple Enterprise Suite (lane W20-A) against the durable enterprise store: a finished SKU is described by a bill-of-materials (component SKU + qty lines), a work order is released for that finished SKU × quantity (only when a BOM exists), and completing the work order records finished-goods production. Work-order status is a pure-Simple fold over an insert-only event ledger (`mfg_wo_events`) — never an UPDATE.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manufacturing / Bill-of-Materials Vertical — define BOM, release + complete WOs

The manufacturing flow of the Simple Enterprise Suite (lane W20-A) against the durable enterprise store: a finished SKU is described by a bill-of-materials (component SKU + qty lines), a work order is released for that finished SKU × quantity (only when a BOM exists), and completing the work order records finished-goods production. Work-order status is a pure-Simple fold over an insert-only event ledger (`mfg_wo_events`) — never an UPDATE.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md (W20-A) |
| Design | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The manufacturing flow of the Simple Enterprise Suite (lane W20-A) against the
durable enterprise store: a finished SKU is described by a bill-of-materials
(component SKU + qty lines), a work order is released for that finished SKU ×
quantity (only when a BOM exists), and completing the work order records
finished-goods production. Work-order status is a pure-Simple fold over an
insert-only event ledger (`mfg_wo_events`) — never an UPDATE.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | cross-tenant / inactive session rejected |
| rbac | forbidden | sales role cannot define a BOM / release a WO |
| validation | invalid-record | release with no BOM for the finished SKU |
| validation | invalid-transition | completing a WO twice (double-complete) |
| idempotency | duplicate-key | replay returns recorded result, one effect |

## Invariants

- a work order cannot be released for a SKU with no BOM.
- status folds "" -> released -> completed; a completed WO cannot re-complete.
- every mutation appends a sha256-chained audit row (verified end to end).
- tenant B sees none of tenant A's BOMs / work orders and cannot mutate them.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md (W20-A)
**Design:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W20-A).

## Scenarios

### manufacturing vertical — BOM, release, complete happy path

#### defines a BOM, releases a WO, completes it, and records production

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines a BOM, releases a WO, completes it, and records production
- Open a clean store and define a 2-line BOM for FG-1
   - Expected: bom_define(store, sk, t, planner, envelope("e2e-bom", "proc.po.create"), "FG-1", bom_lines()).reason equals `accepted`
   - Expected: bom_line_count(store, "tenant-a", "FG-1") equals `2`
- Release a work order for 5 units of FG-1
   - Expected: work_order_release(store, sk, t, planner, envelope("e2e-rel", "proc.po.create"), "WO-1", "FG-1", 5).reason equals `accepted`
   - Expected: wo_status(store, "tenant-a", "WO-1") equals `released`
   - Expected: produced_qty(store, "tenant-a", "FG-1") equals `0`
- Complete the work order — production booked, status completed
   - Expected: work_order_complete(store, sk, t, planner, envelope("e2e-cmp", "proc.po.receive"), "WO-1").reason equals `accepted`
   - Expected: wo_status(store, "tenant-a", "WO-1") equals `completed`
   - Expected: produced_qty(store, "tenant-a", "FG-1") equals `5`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defines a BOM, releases a WO, completes it, and records production")
step("Open a clean store and define a 2-line BOM for FG-1")
val store = fresh_store("e2e")
val t = tenant_a()
val planner = planner_a()
val sk = session_for(planner, t)
expect(bom_define(store, sk, t, planner, envelope("e2e-bom", "proc.po.create"), "FG-1", bom_lines()).reason).to_equal("accepted")
expect(bom_exists(store, "tenant-a", "FG-1")).to_be(true)
expect(bom_line_count(store, "tenant-a", "FG-1")).to_equal(2)

step("Release a work order for 5 units of FG-1")
expect(work_order_release(store, sk, t, planner, envelope("e2e-rel", "proc.po.create"), "WO-1", "FG-1", 5).reason).to_equal("accepted")
expect(wo_status(store, "tenant-a", "WO-1")).to_equal("released")
expect(produced_qty(store, "tenant-a", "FG-1")).to_equal(0)

step("Complete the work order — production booked, status completed")
expect(work_order_complete(store, sk, t, planner, envelope("e2e-cmp", "proc.po.receive"), "WO-1").reason).to_equal("accepted")
expect(wo_status(store, "tenant-a", "WO-1")).to_equal("completed")
expect(produced_qty(store, "tenant-a", "FG-1")).to_equal(5)

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### manufacturing vertical — guarded denials (reproduce-first)

#### denies an unauthorized actor at the rbac rung

- denies an unauthorized actor at the rbac rung
- A sales-role actor attempts to define a BOM — rbac fires 'forbidden'
   - Expected: r.reason equals `forbidden`
- A sales-role actor cannot release a work order either
   - Expected: work_order_release(store, session_for(clerk, t), t, clerk, envelope("rbac-rel", "proc.po.create"), "WO-9", "FG-1", 1).reason equals `forbidden`
- An inactive session is rejected before rbac
   - Expected: work_order_release(store, dead, t, planner, envelope("rbac-dead", "proc.po.create"), "WO-9", "FG-1", 1).reason equals `invalid-session`
- No work order was opened by any denial
   - Expected: wo_status(store, "tenant-a", "WO-9") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an unauthorized actor at the rbac rung")
val store = seed_bom("rbac")
val t = tenant_a()
step("A sales-role actor attempts to define a BOM — rbac fires 'forbidden'")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val r = bom_define(store, session_for(clerk, t), t, clerk, envelope("rbac-bom", "proc.po.create"), "FG-2", bom_lines())
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
step("A sales-role actor cannot release a work order either")
expect(work_order_release(store, session_for(clerk, t), t, clerk, envelope("rbac-rel", "proc.po.create"), "WO-9", "FG-1", 1).reason).to_equal("forbidden")
step("An inactive session is rejected before rbac")
val planner = planner_a()
var dead = session_for(planner, t)
dead.active = false
expect(work_order_release(store, dead, t, planner, envelope("rbac-dead", "proc.po.create"), "WO-9", "FG-1", 1).reason).to_equal("invalid-session")
step("No work order was opened by any denial")
expect(wo_status(store, "tenant-a", "WO-9")).to_equal("")
store_close(store)
```

</details>

#### denies releasing a work order for a SKU with no BOM (invalid-record)

- denies releasing a work order for a SKU with no BOM (invalid-record)
- FG-404 has no BOM defined
- Releasing a WO for FG-404 is denied with invalid-record
   - Expected: r.reason equals `invalid-record`
   - Expected: r.detail equals `no-bom:FG-404`
- No effect — the work order was never opened
   - Expected: wo_status(store, "tenant-a", "WO-404") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies releasing a work order for a SKU with no BOM (invalid-record)")
val store = seed_bom("nobom")
val t = tenant_a()
val planner = planner_a()
val sk = session_for(planner, t)
step("FG-404 has no BOM defined")
expect(bom_exists(store, "tenant-a", "FG-404")).to_be(false)
step("Releasing a WO for FG-404 is denied with invalid-record")
val r = work_order_release(store, sk, t, planner, envelope("nb-rel", "proc.po.create"), "WO-404", "FG-404", 1)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")
expect(r.detail).to_equal("no-bom:FG-404")
step("No effect — the work order was never opened")
expect(wo_status(store, "tenant-a", "WO-404")).to_equal("")
store_close(store)
```

</details>

#### denies completing an already-completed work order (invalid-transition)

- denies completing an already-completed work order (invalid-transition)
- Release then complete WO-1 — accepted
   - Expected: work_order_release(store, sk, t, planner, envelope("dbl-rel", "proc.po.create"), "WO-1", "FG-1", 4).reason equals `accepted`
   - Expected: work_order_complete(store, sk, t, planner, envelope("dbl-cmp1", "proc.po.receive"), "WO-1").reason equals `accepted`
   - Expected: wo_status(store, "tenant-a", "WO-1") equals `completed`
- A SECOND complete with a NEW key is denied invalid-transition
   - Expected: r.reason equals `invalid-transition`
   - Expected: r.detail equals `not-released:WO-1:status=completed`
- Completing a never-released work order is likewise invalid-transition
   - Expected: work_order_complete(store, sk, t, planner, envelope("dbl-cmp3", "proc.po.receive"), "WO-ghost").reason equals `invalid-transition`
- Production stays at exactly one completion's worth
   - Expected: produced_qty(store, "tenant-a", "FG-1") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies completing an already-completed work order (invalid-transition)")
val store = seed_bom("dbl")
val t = tenant_a()
val planner = planner_a()
val sk = session_for(planner, t)
step("Release then complete WO-1 — accepted")
expect(work_order_release(store, sk, t, planner, envelope("dbl-rel", "proc.po.create"), "WO-1", "FG-1", 4).reason).to_equal("accepted")
expect(work_order_complete(store, sk, t, planner, envelope("dbl-cmp1", "proc.po.receive"), "WO-1").reason).to_equal("accepted")
expect(wo_status(store, "tenant-a", "WO-1")).to_equal("completed")
step("A SECOND complete with a NEW key is denied invalid-transition")
val r = work_order_complete(store, sk, t, planner, envelope("dbl-cmp2", "proc.po.receive"), "WO-1")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-transition")
expect(r.detail).to_equal("not-released:WO-1:status=completed")
step("Completing a never-released work order is likewise invalid-transition")
expect(work_order_complete(store, sk, t, planner, envelope("dbl-cmp3", "proc.po.receive"), "WO-ghost").reason).to_equal("invalid-transition")
step("Production stays at exactly one completion's worth")
expect(produced_qty(store, "tenant-a", "FG-1")).to_equal(4)
store_close(store)
```

</details>

### manufacturing vertical — idempotent replay produces exactly one effect

#### replaying the same complete command changes nothing

- replaying the same complete command changes nothing
- Release then complete WO-1 with a fixed complete key
   - Expected: work_order_release(store, sk, t, planner, envelope("rp-rel", "proc.po.create"), "WO-1", "FG-1", 6).reason equals `accepted`
   - Expected: work_order_complete(store, sk, t, planner, envelope("rp-cmp", "proc.po.receive"), "WO-1").reason equals `accepted`
- Replay the SAME complete idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `WO-1`
- No second effect — production and outbox unchanged
   - Expected: produced_qty(store, "tenant-a", "FG-1") equals `produced_after`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying the same complete command changes nothing")
val store = seed_bom("replay")
val t = tenant_a()
val planner = planner_a()
val sk = session_for(planner, t)
step("Release then complete WO-1 with a fixed complete key")
expect(work_order_release(store, sk, t, planner, envelope("rp-rel", "proc.po.create"), "WO-1", "FG-1", 6).reason).to_equal("accepted")
expect(work_order_complete(store, sk, t, planner, envelope("rp-cmp", "proc.po.receive"), "WO-1").reason).to_equal("accepted")
val produced_after = produced_qty(store, "tenant-a", "FG-1")
val outbox_after = outbox_pending(store, "tenant-a").len()
step("Replay the SAME complete idempotency key")
val replay = work_order_complete(store, sk, t, planner, envelope("rp-cmp", "proc.po.receive"), "WO-1")
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("WO-1")
step("No second effect — production and outbox unchanged")
expect(produced_qty(store, "tenant-a", "FG-1")).to_equal(produced_after)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after)
store_close(store)
```

</details>

### manufacturing vertical — tenant isolation

#### tenant B sees none of tenant A's BOMs / work orders and cannot mutate them

- tenant B sees none of tenant A's BOMs / work orders and cannot mutate them
- Tenant B sees no BOM for FG-1 and no production
   - Expected: produced_qty(store, "tenant-b", "FG-1") equals `0`
- A tenant-B planner releasing against FG-1 is denied (its own BOM is absent)
   - Expected: r.reason equals `invalid-record`
   - Expected: r.detail equals `no-bom:FG-1`
- A cross-tenant session (tenant-B session against tenant-A context) is rejected outright
   - Expected: work_order_release(store, sbb, ta, planner_b, envelope("iso-x", "proc.po.create"), "WO-B", "FG-1", 1).reason equals `invalid-session`
- Tenant A's BOM is untouched
   - Expected: bom_line_count(store, "tenant-a", "FG-1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B sees none of tenant A's BOMs / work orders and cannot mutate them")
val store = seed_bom("isolation")
step("Tenant B sees no BOM for FG-1 and no production")
expect(bom_exists(store, "tenant-b", "FG-1")).to_be(false)
expect(produced_qty(store, "tenant-b", "FG-1")).to_equal(0)
step("A tenant-B planner releasing against FG-1 is denied (its own BOM is absent)")
val tb = tenant_b()
val planner_b = ActorContext(actor_id: "planner-b", role: "procurement")
val sbb = session_for(planner_b, tb)
val r = work_order_release(store, sbb, tb, planner_b, envelope("iso-rel", "proc.po.create"), "WO-B", "FG-1", 1)
expect(r.reason).to_equal("invalid-record")
expect(r.detail).to_equal("no-bom:FG-1")
step("A cross-tenant session (tenant-B session against tenant-A context) is rejected outright")
val ta = tenant_a()
expect(work_order_release(store, sbb, ta, planner_b, envelope("iso-x", "proc.po.create"), "WO-B", "FG-1", 1).reason).to_equal("invalid-session")
step("Tenant A's BOM is untouched")
expect(bom_line_count(store, "tenant-a", "FG-1")).to_equal(2)
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

- **Plan:** `.spipe/simple_enterprise_suite/state.md (W20-A)`
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

- Canonical SPipe generation for source `1c68a4d0b729960f3c1413272c1969ba2f1c6d35fd2c11cea1a521e223c352ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c68a4d0b729960f3c1413272c1969ba2f1c6d35fd2c11cea1a521e223c352ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c68a4d0b729960f3c1413272c1969ba2f1c6d35fd2c11cea1a521e223c352ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines a BOM, releases a WO, completes it, and records production' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies an unauthorized actor at the rbac rung' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_manufacturing_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies releasing a work order for a SKU with no BOM (invalid-record)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
