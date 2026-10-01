# CRM / Sales-Pipeline Vertical — scenario over the durable store

> The CRM vertical of the Simple Enterprise Suite, exercised against the durable enterprise store: a sales rep creates a lead, qualifies it, opens an opportunity with a Money amount, and advances it to won; the pipeline summary folds counts and total Money per stage; every mutation runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CRM / Sales-Pipeline Vertical — scenario over the durable store

The CRM vertical of the Simple Enterprise Suite, exercised against the durable enterprise store: a sales rep creates a lead, qualifies it, opens an opportunity with a Money amount, and advances it to won; the pipeline summary folds counts and total Money per stage; every mutation runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The CRM vertical of the Simple Enterprise Suite, exercised against the durable
enterprise store: a sales rep creates a lead, qualifies it, opens an
opportunity with a Money amount, and advances it to won; the pipeline summary
folds counts and total Money per stage; every mutation runs the frozen guarded
sequence (session -> rbac -> validation -> idempotency -> effects in one UoW)
and chains a sha256 audit record.

## Guarded sequence proven here (reproduce-first for each denial)

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| rbac | forbidden | an unauthorized role cannot create a lead |
| validation | invalid-transition | qualifying an already-qualified lead; opening from an unqualified lead; advancing to an illegal stage |
| idempotency | duplicate-key | replay returns recorded result, exactly one effect |
| tenancy | not-found / invalid-session | tenant B cannot see or mutate tenant A's leads |

## Invariants

- current stage is a pure fold over the insert-only stage stream (never UPDATE);
- an illegal stage move is denied with the closed-set reason invalid-transition;
- a replayed command produces exactly one effect (opportunity count unchanged);
- the session tenant is authority — a cross-tenant session is rejected outright.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W19-A).

## Scenarios

### crm vertical — one complete pipeline end to end

#### lead -> qualify -> opportunity -> won with a pipeline summary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lead -> qualify -> opportunity -> won with a pipeline summary
- Open a clean store
- Create a lead — stage folds to 'new'
   - Expected: created.reason equals `accepted`
   - Expected: crm_lead_stage(store, "tenant-a", "lead-1") equals `new`
- Qualify the lead — stage folds to 'qualified'
   - Expected: qualified.reason equals `accepted`
   - Expected: crm_lead_stage(store, "tenant-a", "lead-1") equals `qualified`
- Open an opportunity with a Money amount — stage 'open'
   - Expected: opened.reason equals `accepted`
   - Expected: crm_opp_stage(store, "tenant-a", "opp-1") equals `open`
- Pipeline summary reflects one open opportunity worth 50000
   - Expected: mid.open.count equals `1`
   - Expected: mid.open.total_cents equals `50000`
   - Expected: mid.won.count equals `0`
   - Expected: mid.currency equals `USD`
- Advance the opportunity to won
   - Expected: won.reason equals `accepted`
   - Expected: crm_opp_stage(store, "tenant-a", "opp-1") equals `won`
- Pipeline summary now shows the opportunity won
   - Expected: fin.open.count equals `0`
   - Expected: fin.won.count equals `1`
   - Expected: fin.won.total_cents equals `50000`
- The audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lead -> qualify -> opportunity -> won with a pipeline summary")
step("Open a clean store")
val store = fresh_store("e2e")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)

step("Create a lead — stage folds to 'new'")
val created = crm_lead_create(store, s, t, rep, envelope("lead-k1", "crm.lead.create"), "lead-1", "Acme Corp")
expect(created.reason).to_equal("accepted")
expect(reason_allowed(created.reason)).to_be(true)
expect(crm_lead_stage(store, "tenant-a", "lead-1")).to_equal("new")

step("Qualify the lead — stage folds to 'qualified'")
val qualified = crm_lead_qualify(store, s, t, rep, envelope("qual-k1", "crm.lead.qualify"), "lead-1")
expect(qualified.reason).to_equal("accepted")
expect(crm_lead_stage(store, "tenant-a", "lead-1")).to_equal("qualified")

step("Open an opportunity with a Money amount — stage 'open'")
val opened = crm_opportunity_open(store, s, t, rep, envelope("opp-k1", "crm.opportunity.open"), "opp-1", "lead-1", usd(50000))
expect(opened.reason).to_equal("accepted")
expect(crm_opp_stage(store, "tenant-a", "opp-1")).to_equal("open")

step("Pipeline summary reflects one open opportunity worth 50000")
val mid = crm_pipeline_summary(store, "tenant-a")
expect(mid.open.count).to_equal(1)
expect(mid.open.total_cents).to_equal(50000)
expect(mid.won.count).to_equal(0)
expect(mid.currency).to_equal("USD")

step("Advance the opportunity to won")
val won = crm_opportunity_advance(store, s, t, rep, envelope("adv-k1", "crm.opportunity.advance"), "opp-1", "won")
expect(won.reason).to_equal("accepted")
expect(crm_opp_stage(store, "tenant-a", "opp-1")).to_equal("won")

step("Pipeline summary now shows the opportunity won")
val fin = crm_pipeline_summary(store, "tenant-a")
expect(fin.open.count).to_equal(0)
expect(fin.won.count).to_equal(1)
expect(fin.won.total_cents).to_equal(50000)

step("The audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### crm vertical — rbac denies an unauthorized actor

#### reproduce: a viewer cannot create a lead (forbidden)

- reproduce: a viewer cannot create a lead (forbidden)
- Attempt lead_create as a viewer role
   - Expected: r.reason equals `forbidden`
- No lead was created
   - Expected: crm_lead_stage(store, "tenant-a", "lead-x") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a viewer cannot create a lead (forbidden)")
val store = fresh_store("rbac")
val t = tenant_a()
val viewer = viewer_a()
step("Attempt lead_create as a viewer role")
val r = crm_lead_create(store, session_for(viewer, t), t, viewer, envelope("k-r", "crm.lead.create"), "lead-x", "Nope Inc")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(reason_allowed(r.reason)).to_be(true)
step("No lead was created")
expect(crm_lead_stage(store, "tenant-a", "lead-x")).to_equal("")
store_close(store)
```

</details>

### crm vertical — invalid stage transitions are denied

#### reproduce: re-qualifying a qualified lead is invalid-transition

- reproduce: re-qualifying a qualified lead is invalid-transition
- Qualify again with a FRESH key — the lead is no longer 'new'
   - Expected: again.reason equals `invalid-transition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: re-qualifying a qualified lead is invalid-transition")
val store = fresh_store("bad_lead_trans")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
crm_lead_create(store, s, t, rep, envelope("l", "crm.lead.create"), "lead-2", "Beta LLC")
crm_lead_qualify(store, s, t, rep, envelope("q", "crm.lead.qualify"), "lead-2")
step("Qualify again with a FRESH key — the lead is no longer 'new'")
val again = crm_lead_qualify(store, s, t, rep, envelope("q2", "crm.lead.qualify"), "lead-2")
expect(again.ok).to_be(false)
expect(again.reason).to_equal("invalid-transition")
expect(reason_allowed(again.reason)).to_be(true)
store_close(store)
```

</details>

#### reproduce: opening from an unqualified lead is invalid-transition

- reproduce: opening from an unqualified lead is invalid-transition
- Open an opportunity while lead-3 is still 'new'
   - Expected: r.reason equals `invalid-transition`
   - Expected: crm_opp_stage(store, "tenant-a", "opp-3") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: opening from an unqualified lead is invalid-transition")
val store = fresh_store("bad_open")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
crm_lead_create(store, s, t, rep, envelope("l3", "crm.lead.create"), "lead-3", "Gamma Co")
step("Open an opportunity while lead-3 is still 'new'")
val r = crm_opportunity_open(store, s, t, rep, envelope("o3", "crm.opportunity.open"), "opp-3", "lead-3", usd(1000))
expect(r.reason).to_equal("invalid-transition")
expect(crm_opp_stage(store, "tenant-a", "opp-3")).to_equal("")
store_close(store)
```

</details>

#### reproduce: advancing an open opportunity to a bogus stage is invalid-transition

- reproduce: advancing an open opportunity to a bogus stage is invalid-transition
- Advance to a stage outside {won, lost}
   - Expected: r.reason equals `invalid-transition`
   - Expected: crm_opp_stage(store, "tenant-a", "opp-4") equals `open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: advancing an open opportunity to a bogus stage is invalid-transition")
val store = fresh_store("bad_advance")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
crm_lead_create(store, s, t, rep, envelope("l4", "crm.lead.create"), "lead-4", "Delta Co")
crm_lead_qualify(store, s, t, rep, envelope("q4", "crm.lead.qualify"), "lead-4")
crm_opportunity_open(store, s, t, rep, envelope("o4", "crm.opportunity.open"), "opp-4", "lead-4", usd(2000))
step("Advance to a stage outside {won, lost}")
val r = crm_opportunity_advance(store, s, t, rep, envelope("a4", "crm.opportunity.advance"), "opp-4", "reopened")
expect(r.reason).to_equal("invalid-transition")
expect(crm_opp_stage(store, "tenant-a", "opp-4")).to_equal("open")
store_close(store)
```

</details>

### crm vertical — idempotent replay produces exactly one effect

#### replaying an opportunity_open changes nothing

- replaying an opportunity_open changes nothing
- Open the opportunity once
   - Expected: first.reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `opp-5`
- No second effect — pipeline count and outbox unchanged
   - Expected: crm_pipeline_summary(store, "tenant-a").open.count equals `open_after_first`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying an opportunity_open changes nothing")
val store = fresh_store("replay")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
crm_lead_create(store, s, t, rep, envelope("l5", "crm.lead.create"), "lead-5", "Epsilon Co")
crm_lead_qualify(store, s, t, rep, envelope("q5", "crm.lead.qualify"), "lead-5")

step("Open the opportunity once")
val first = crm_opportunity_open(store, s, t, rep, envelope("same-key", "crm.opportunity.open"), "opp-5", "lead-5", usd(7500))
expect(first.reason).to_equal("accepted")
val open_after_first = crm_pipeline_summary(store, "tenant-a").open.count
val outbox_after_first = outbox_pending(store, "tenant-a").len()

step("Replay the SAME idempotency key")
val replay = crm_opportunity_open(store, s, t, rep, envelope("same-key", "crm.opportunity.open"), "opp-5", "lead-5", usd(7500))
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("opp-5")

step("No second effect — pipeline count and outbox unchanged")
expect(crm_pipeline_summary(store, "tenant-a").open.count).to_equal(open_after_first)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
store_close(store)
```

</details>

### crm vertical — tenant isolation

#### tenant B cannot see or mutate tenant A's leads

- tenant B cannot see or mutate tenant A's leads
- Tenant B sees no stage for tenant A's lead
   - Expected: crm_lead_stage(store, "tenant-b", "lead-a") equals ``
- A tenant-B rep cannot qualify tenant A's lead — not-found in B's scope
   - Expected: r.reason equals `invalid-record`
- A cross-tenant session (B token presented with A as authority) is rejected outright
   - Expected: r2.reason equals `invalid-session`
- Tenant A's lead is untouched — still 'new'
   - Expected: crm_lead_stage(store, "tenant-a", "lead-a") equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B cannot see or mutate tenant A's leads")
val store = fresh_store("isolation")
val ta = tenant_a()
val rep = rep_a()
val sa = session_for(rep, ta)
crm_lead_create(store, sa, ta, rep, envelope("la", "crm.lead.create"), "lead-a", "Alpha Lead")

step("Tenant B sees no stage for tenant A's lead")
expect(crm_lead_stage(store, "tenant-b", "lead-a")).to_equal("")

step("A tenant-B rep cannot qualify tenant A's lead — not-found in B's scope")
val tb = tenant_b()
val rep_b = ActorContext(actor_id: "rep-b", role: "sales")
val sb = session_for(rep_b, tb)
val r = crm_lead_qualify(store, sb, tb, rep_b, envelope("qb", "crm.lead.qualify"), "lead-a")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")

step("A cross-tenant session (B token presented with A as authority) is rejected outright")
val forged = SessionContext(token: "tok-rep-b", actor_id: "rep-b", tenant_id: "tenant-b", active: true)
val r2 = crm_lead_qualify(store, forged, ta, rep_b, envelope("qb2", "crm.lead.qualify"), "lead-a")
expect(r2.reason).to_equal("invalid-session")

step("Tenant A's lead is untouched — still 'new'")
expect(crm_lead_stage(store, "tenant-a", "lead-a")).to_equal("new")
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
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20f22ee7bc0e0de9058e7449b77fd86db10f83a0d2e239c74e66a01650c720a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20f22ee7bc0e0de9058e7449b77fd86db10f83a0d2e239c74e66a01650c720a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20f22ee7bc0e0de9058e7449b77fd86db10f83a0d2e239c74e66a01650c720a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lead -> qualify -> opportunity -> won with a pipeline summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: a viewer cannot create a lead (forbidden)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_crm_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: re-qualifying a qualified lead is invalid-transition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
