# Loyalty / Rewards-Points Vertical — earn, redeem over an insert-only ledger

> The rewards-points flow of the Simple Enterprise Suite (lane W22-B) against the durable enterprise store: points are earned into a member's balance and redeemed against it. The balance is a pure-Simple fold over an insert-only signed points ledger (`loyalty_events`, earn stored +, redeem stored −) — never an UPDATE.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loyalty / Rewards-Points Vertical — earn, redeem over an insert-only ledger

The rewards-points flow of the Simple Enterprise Suite (lane W22-B) against the durable enterprise store: points are earned into a member's balance and redeemed against it. The balance is a pure-Simple fold over an insert-only signed points ledger (`loyalty_events`, earn stored +, redeem stored −) — never an UPDATE.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md (W22-B) |
| Design | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The rewards-points flow of the Simple Enterprise Suite (lane W22-B) against
the durable enterprise store: points are earned into a member's balance and
redeemed against it. The balance is a pure-Simple fold over an insert-only
signed points ledger (`loyalty_events`, earn stored +, redeem stored −) —
never an UPDATE.

## Guarded sequence proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | cross-tenant / inactive session rejected |
| rbac | forbidden | clerk role cannot earn/redeem points |
| validation | invalid-record | non-positive points rejected |
| validation | insufficient-stock | redeem beyond balance (closest closed-set reason) |
| idempotency | duplicate-key | replay returns recorded result, one effect |

## Invariants

- balance = Σ(delta); earn raises it, redeem lowers it, no UPDATE.
- over-redeem (points > balance) denies `insufficient-stock`, balance unchanged.
- tenant B sees none of tenant A's points and cannot redeem them.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md (W22-B)
**Design:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W22-B).

## Scenarios

### loyalty vertical — earn, redeem, and balance math

#### earns points, redeems within balance, and derives correct balances

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- earns points, redeems within balance, and derives correct balances
- Open a clean store and earn 100 points for MEM-1
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `0`
   - Expected: loyalty_earn(store, sk, t, agent, envelope("e2e-earn", "loyalty.points.earn"), "MEM-1", 100).reason equals `accepted`
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `100`
- Earn 40 more — balance rises to 140
   - Expected: loyalty_earn(store, sk, t, agent, envelope("e2e-earn2", "loyalty.points.earn"), "MEM-1", 40).reason equals `accepted`
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `140`
- Redeem 90 within balance — balance falls to 50
   - Expected: loyalty_redeem(store, sk, t, agent, envelope("e2e-rdm", "loyalty.points.redeem"), "MEM-1", 90).reason equals `accepted`
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `50`
- A different member is independent (no cross-member bleed)
   - Expected: loyalty_balance(store, "tenant-a", "MEM-2") equals `0`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("earns points, redeems within balance, and derives correct balances")
step("Open a clean store and earn 100 points for MEM-1")
val store = fresh_store("e2e")
val t = tenant_a()
val agent = agent_a()
val sk = session_for(agent, t)
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(0)
expect(loyalty_earn(store, sk, t, agent, envelope("e2e-earn", "loyalty.points.earn"), "MEM-1", 100).reason).to_equal("accepted")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(100)

step("Earn 40 more — balance rises to 140")
expect(loyalty_earn(store, sk, t, agent, envelope("e2e-earn2", "loyalty.points.earn"), "MEM-1", 40).reason).to_equal("accepted")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(140)

step("Redeem 90 within balance — balance falls to 50")
expect(loyalty_redeem(store, sk, t, agent, envelope("e2e-rdm", "loyalty.points.redeem"), "MEM-1", 90).reason).to_equal("accepted")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(50)

step("A different member is independent (no cross-member bleed)")
expect(loyalty_balance(store, "tenant-a", "MEM-2")).to_equal(0)

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### loyalty vertical — guarded denials (reproduce-first)

#### denies an unauthorized actor at the rbac rung

- denies an unauthorized actor at the rbac rung
- A non-sales/non-admin actor attempts an earn — rbac fires 'forbidden'
   - Expected: r.reason equals `forbidden`
- An inactive session is rejected before rbac
   - Expected: loyalty_earn(store, dead, t, agent, envelope("rbac-dead", "loyalty.points.earn"), "MEM-1", 1).reason equals `invalid-session`
- The balance is untouched by every denial
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an unauthorized actor at the rbac rung")
val store = seed_earned("rbac")
val t = tenant_a()
step("A non-sales/non-admin actor attempts an earn — rbac fires 'forbidden'")
val clerk = ActorContext(actor_id: "clerk-1", role: "procurement")
val r = loyalty_earn(store, session_for(clerk, t), t, clerk, envelope("rbac-earn", "loyalty.points.earn"), "MEM-1", 5)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
step("An inactive session is rejected before rbac")
val agent = agent_a()
var dead = session_for(agent, t)
dead.active = false
expect(loyalty_earn(store, dead, t, agent, envelope("rbac-dead", "loyalty.points.earn"), "MEM-1", 1).reason).to_equal("invalid-session")
step("The balance is untouched by every denial")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(100)
store_close(store)
```

</details>

#### denies non-positive points with invalid-record

- denies non-positive points with invalid-record
- Earning 0 points is invalid-record
   - Expected: loyalty_earn(store, sk, t, agent, envelope("inv-earn0", "loyalty.points.earn"), "MEM-1", 0).reason equals `invalid-record`
- Redeeming a negative amount is invalid-record
   - Expected: loyalty_redeem(store, sk, t, agent, envelope("inv-rdmneg", "loyalty.points.redeem"), "MEM-1", -5).reason equals `invalid-record`
- Balance unchanged
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies non-positive points with invalid-record")
val store = seed_earned("invalid")
val t = tenant_a()
val agent = agent_a()
val sk = session_for(agent, t)
step("Earning 0 points is invalid-record")
expect(loyalty_earn(store, sk, t, agent, envelope("inv-earn0", "loyalty.points.earn"), "MEM-1", 0).reason).to_equal("invalid-record")
step("Redeeming a negative amount is invalid-record")
expect(loyalty_redeem(store, sk, t, agent, envelope("inv-rdmneg", "loyalty.points.redeem"), "MEM-1", -5).reason).to_equal("invalid-record")
step("Balance unchanged")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(100)
store_close(store)
```

</details>

#### denies an over-redeem with the closed-set reason and no effect

- denies an over-redeem with the closed-set reason and no effect
- Balance is 100
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `100`
- Attempt to redeem 150 — only 100 available, must be denied
   - Expected: r.reason equals `insufficient-stock`
   - Expected: r.detail equals `over-redeem:MEM-1:balance=100:got=150`
- No effect — balance still 100
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an over-redeem with the closed-set reason and no effect")
val store = seed_earned("overredeem")
val t = tenant_a()
val agent = agent_a()
val sk = session_for(agent, t)
step("Balance is 100")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(100)
step("Attempt to redeem 150 — only 100 available, must be denied")
val r = loyalty_redeem(store, sk, t, agent, envelope("or-1", "loyalty.points.redeem"), "MEM-1", 150)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("insufficient-stock")
expect(r.detail).to_equal("over-redeem:MEM-1:balance=100:got=150")
step("No effect — balance still 100")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(100)
store_close(store)
```

</details>

### loyalty vertical — idempotent replay produces exactly one effect

#### replaying the same earn command changes nothing

- replaying the same earn command changes nothing
- Earn once with a fixed key
   - Expected: loyalty_earn(store, sk, t, agent, envelope("same-key", "loyalty.points.earn"), "MEM-1", 30).reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `MEM-1`
- No second earn — balance and outbox unchanged
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `bal_after`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying the same earn command changes nothing")
val store = seed_earned("replay")
val t = tenant_a()
val agent = agent_a()
val sk = session_for(agent, t)
step("Earn once with a fixed key")
expect(loyalty_earn(store, sk, t, agent, envelope("same-key", "loyalty.points.earn"), "MEM-1", 30).reason).to_equal("accepted")
val bal_after = loyalty_balance(store, "tenant-a", "MEM-1")
val outbox_after = outbox_pending(store, "tenant-a").len()
step("Replay the SAME idempotency key")
val replay = loyalty_earn(store, sk, t, agent, envelope("same-key", "loyalty.points.earn"), "MEM-1", 30)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("MEM-1")
step("No second earn — balance and outbox unchanged")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(bal_after)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after)
store_close(store)
```

</details>

### loyalty vertical — tenant isolation

#### tenant B sees none of tenant A's points and cannot redeem them

- tenant B sees none of tenant A's points and cannot redeem them
- Tenant B sees zero balance for the same member id
   - Expected: loyalty_balance(store, "tenant-b", "MEM-1") equals `0`
- A tenant-B agent redeeming against tenant A's points is denied (its own balance is 0)
   - Expected: loyalty_redeem(store, sbb, tb, agent_b, envelope("iso-rdm", "loyalty.points.redeem"), "MEM-1", 1).reason equals `insufficient-stock`
- A cross-tenant session (tenant-B session against tenant-A context) is rejected outright
   - Expected: loyalty_earn(store, sbb, ta, agent_b, envelope("iso-earn", "loyalty.points.earn"), "MEM-1", 1).reason equals `invalid-session`
- Tenant A's balance is untouched
   - Expected: loyalty_balance(store, "tenant-a", "MEM-1") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B sees none of tenant A's points and cannot redeem them")
val store = seed_earned("isolation")
step("Tenant B sees zero balance for the same member id")
expect(loyalty_balance(store, "tenant-b", "MEM-1")).to_equal(0)
step("A tenant-B agent redeeming against tenant A's points is denied (its own balance is 0)")
val tb = tenant_b()
val agent_b = ActorContext(actor_id: "agent-b", role: "sales")
val sbb = session_for(agent_b, tb)
expect(loyalty_redeem(store, sbb, tb, agent_b, envelope("iso-rdm", "loyalty.points.redeem"), "MEM-1", 1).reason).to_equal("insufficient-stock")
step("A cross-tenant session (tenant-B session against tenant-A context) is rejected outright")
val ta = tenant_a()
expect(loyalty_earn(store, sbb, ta, agent_b, envelope("iso-earn", "loyalty.points.earn"), "MEM-1", 1).reason).to_equal("invalid-session")
step("Tenant A's balance is untouched")
expect(loyalty_balance(store, "tenant-a", "MEM-1")).to_equal(100)
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

- **Plan:** `.spipe/simple_enterprise_suite/state.md (W22-B)`
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

- Canonical SPipe generation for source `a582365e63bfe7f17b17db49b2e008645bc0a808f4134c2cf15d808115dd18ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a582365e63bfe7f17b17db49b2e008645bc0a808f4134c2cf15d808115dd18ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a582365e63bfe7f17b17db49b2e008645bc0a808f4134c2cf15d808115dd18ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'earns points, redeems within balance, and derives correct balances' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies an unauthorized actor at the rbac rung' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_loyalty_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies non-positive points with invalid-record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
