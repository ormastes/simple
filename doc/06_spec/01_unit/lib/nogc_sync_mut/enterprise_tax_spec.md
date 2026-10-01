# Enterprise Tax Vertical — rate config + deterministic compute over the store

> A finance actor sets a tax rate (basis points) for a (jurisdiction, category) under the durable enterprise store, then pure reads compute tax on known amounts with EXACT integer minor-unit results (never floats). Every rate write runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Tax Vertical — rate config + deterministic compute over the store

A finance actor sets a tax rate (basis points) for a (jurisdiction, category) under the durable enterprise store, then pure reads compute tax on known amounts with EXACT integer minor-unit results (never floats). Every rate write runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A finance actor sets a tax rate (basis points) for a (jurisdiction, category)
under the durable enterprise store, then pure reads compute tax on known
amounts with EXACT integer minor-unit results (never floats). Every rate write
runs the frozen guarded sequence (session -> rbac -> validation -> idempotency
-> effects in one UoW) and chains a sha256 audit record.

## Rounding rule proven here

`tax = round_half_up(amount_cents * rate_bp / 10000)` computed on integers as
`(amount_cents*rate_bp + 5000)/10000`. The boundary case 1000 cents @ 875 bp =
87.5 cents rounds UP to 88; 1000 @ 874 bp = 87.4 rounds DOWN to 87 — the two
adjacent rates straddle the half threshold, proving round-HALF-UP exactly.
`tax_breakdown` rounds PER LINE then sums: [1000,1000] @ 875 bp = 88+88 = 176,
NOT the aggregate 2000 @ 875 = 175 — proving line-level rounding.

## Guarded sequence proven (reproduce-first for each denial)

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| rbac | forbidden | a `sales` actor cannot set a tax rate |
| idempotency | duplicate-key | replay returns recorded result, no second effect |

Plus: latest-rate-wins after a second `tax_rate_set`; tenant isolation
(tenant-B compute uses only tenant-B rates).

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W20-B).

## Scenarios

### tax vertical — set a rate then compute exact tax

#### finance sets 875 bp and tax_for rounds half-up on the minor unit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finance sets 875 bp and tax_for rounds half-up on the minor unit
- Open a clean store
- Set an 8.75% rate (875 bp) for (US-CA, standard)
   - Expected: set.reason equals `accepted`
   - Expected: tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard") equals `875`
- Boundary case: 1000 cents @ 875 bp = 87.5 -> rounds UP to 88
   - Expected: tax_for(store, s, t, cfo, "US-CA", "standard", usd(1000)).amount_cents equals `88`
- Exact case: 2000 cents @ 875 bp = 175.0 -> 175
   - Expected: tax_for(store, s, t, cfo, "US-CA", "standard", usd(2000)).amount_cents equals `175`
- Currency is preserved on the returned Money
   - Expected: tax_for(store, s, t, cfo, "US-CA", "standard", usd(1000)).currency equals `USD`
- The audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finance sets 875 bp and tax_for rounds half-up on the minor unit")
step("Open a clean store")
val store = fresh_store("compute")
val t = tenant_a()
val cfo = cfo_a()
val s = session_for(cfo, t)

step("Set an 8.75% rate (875 bp) for (US-CA, standard)")
val set = tax_rate_set(store, s, t, cfo, envelope("r-1"), "US-CA", "standard", 875)
expect(set.reason).to_equal("accepted")
expect(reason_allowed(set.reason)).to_be(true)
expect(tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard")).to_equal(875)

step("Boundary case: 1000 cents @ 875 bp = 87.5 -> rounds UP to 88")
expect(tax_for(store, s, t, cfo, "US-CA", "standard", usd(1000)).amount_cents).to_equal(88)

step("Exact case: 2000 cents @ 875 bp = 175.0 -> 175")
expect(tax_for(store, s, t, cfo, "US-CA", "standard", usd(2000)).amount_cents).to_equal(175)

step("Currency is preserved on the returned Money")
expect(tax_for(store, s, t, cfo, "US-CA", "standard", usd(1000)).currency).to_equal("USD")

step("The audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### tax vertical — round-half-up boundary is exact

#### reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)

- reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)
- The pure rounding helper straddles the half threshold
   - Expected: tax_round_half_up(1000, 875) equals `88`
   - Expected: tax_round_half_up(1000, 874) equals `87`
   - Expected: tax_round_half_up(0, 875) equals `0`
   - Expected: tax_round_half_up(1000, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)")
step("The pure rounding helper straddles the half threshold")
# 1000*875/10000 = 87.5 exactly -> half rounds away from zero -> 88
expect(tax_round_half_up(1000, 875)).to_equal(88)
# 1000*874/10000 = 87.4 -> below the half -> 87
expect(tax_round_half_up(1000, 874)).to_equal(87)
# a non-positive amount or rate yields 0 (no tax configured == 0%)
expect(tax_round_half_up(0, 875)).to_equal(0)
expect(tax_round_half_up(1000, 0)).to_equal(0)
```

</details>

### tax vertical — line breakdown rounds per line then sums

#### [1000,1000] @ 875 bp = 88+88 = 176, not the aggregate 175

- [1000,1000] @ 875 bp = 88+88 = 176, not the aggregate 175
- Per-line rounding gives 88 for each 1000-cent line
   - Expected: bd.rate_bp equals `875`
   - Expected: bd.lines.len() equals `2`
   - Expected: bd.lines[0].tax_cents equals `88`
   - Expected: bd.lines[1].tax_cents equals `88`
- Total is the SUM of the rounded per-line taxes (176), not the aggregate 175
   - Expected: bd.total_tax_cents equals `176`
   - Expected: tax_round_half_up(2000, 875) equals `175`
   - Expected: bd.currency equals `USD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("[1000,1000] @ 875 bp = 88+88 = 176, not the aggregate 175")
val store = fresh_store("breakdown")
val t = tenant_a()
val cfo = cfo_a()
val s = session_for(cfo, t)
tax_rate_set(store, s, t, cfo, envelope("r-b"), "US-CA", "standard", 875)

step("Per-line rounding gives 88 for each 1000-cent line")
val bd = tax_breakdown(store, s, t, cfo, "US-CA", "standard", [1000, 1000], "USD")
expect(bd.rate_bp).to_equal(875)
expect(bd.lines.len()).to_equal(2)
expect(bd.lines[0].tax_cents).to_equal(88)
expect(bd.lines[1].tax_cents).to_equal(88)

step("Total is the SUM of the rounded per-line taxes (176), not the aggregate 175")
expect(bd.total_tax_cents).to_equal(176)
# aggregate cross-check: 2000 @ 875 = 175.0 -> 175, which differs from 176
expect(tax_round_half_up(2000, 875)).to_equal(175)
expect(bd.currency).to_equal("USD")
store_close(store)
```

</details>

### tax vertical — rbac denies an unauthorized actor

#### reproduce: a sales actor cannot set a tax rate (forbidden)

- reproduce: a sales actor cannot set a tax rate (forbidden)
- Attempt tax_rate_set as a sales role
   - Expected: r.reason equals `forbidden`
- No rate was recorded
   - Expected: tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a sales actor cannot set a tax rate (forbidden)")
val store = fresh_store("rbac")
val t = tenant_a()
val clerk = clerk_a()
step("Attempt tax_rate_set as a sales role")
val r = tax_rate_set(store, session_for(clerk, t), t, clerk, envelope("r-x"), "US-CA", "standard", 500)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(reason_allowed(r.reason)).to_be(true)
step("No rate was recorded")
expect(tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard")).to_equal(-1)
store_close(store)
```

</details>

### tax vertical — latest rate wins (insert-only re-rate)

#### a second tax_rate_set supersedes the first for compute

- a second tax_rate_set supersedes the first for compute
- Set 875 bp, then re-rate to 500 bp with a fresh key
   - Expected: second.reason equals `accepted`
- Effective rate is the latest (500 bp); 1000 cents -> 50
   - Expected: tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard") equals `500`
   - Expected: tax_for(store, s, t, cfo, "US-CA", "standard", usd(1000)).amount_cents equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a second tax_rate_set supersedes the first for compute")
val store = fresh_store("latest")
val t = tenant_a()
val cfo = cfo_a()
val s = session_for(cfo, t)
step("Set 875 bp, then re-rate to 500 bp with a fresh key")
tax_rate_set(store, s, t, cfo, envelope("r-first"), "US-CA", "standard", 875)
val second = tax_rate_set(store, s, t, cfo, envelope("r-second"), "US-CA", "standard", 500)
expect(second.reason).to_equal("accepted")
step("Effective rate is the latest (500 bp); 1000 cents -> 50")
expect(tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard")).to_equal(500)
expect(tax_for(store, s, t, cfo, "US-CA", "standard", usd(1000)).amount_cents).to_equal(50)
store_close(store)
```

</details>

### tax vertical — tenant isolation

#### tenant B compute uses only tenant B rates

- tenant B compute uses only tenant B rates
- Tenant A sets 875 bp; tenant B sets 2000 bp for the SAME keys
- Each tenant's compute reads only its own rate
   - Expected: tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard") equals `875`
   - Expected: tax_effective_rate_bp(store, "tenant-b", "US-CA", "standard") equals `2000`
   - Expected: tax_for(store, sa, ta, cfo_a_actor, "US-CA", "standard", usd(1000)).amount_cents equals `88`
   - Expected: tax_for(store, sb, tb, cfo_b, "US-CA", "standard", usd(1000)).amount_cents equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B compute uses only tenant B rates")
val store = fresh_store("isolation")
val ta = tenant_a()
val cfo_a_actor = cfo_a()
val sa = session_for(cfo_a_actor, ta)
val tb = tenant_b()
val cfo_b = ActorContext(actor_id: "cfo-b", role: "finance")
val sb = session_for(cfo_b, tb)

step("Tenant A sets 875 bp; tenant B sets 2000 bp for the SAME keys")
tax_rate_set(store, sa, ta, cfo_a_actor, envelope("r-a"), "US-CA", "standard", 875)
tax_rate_set(store, sb, tb, cfo_b, envelope("r-b2"), "US-CA", "standard", 2000)

step("Each tenant's compute reads only its own rate")
expect(tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard")).to_equal(875)
expect(tax_effective_rate_bp(store, "tenant-b", "US-CA", "standard")).to_equal(2000)
# 1000 @ 875 = 88 for A; 1000 @ 2000 (20%) = 200 for B
expect(tax_for(store, sa, ta, cfo_a_actor, "US-CA", "standard", usd(1000)).amount_cents).to_equal(88)
expect(tax_for(store, sb, tb, cfo_b, "US-CA", "standard", usd(1000)).amount_cents).to_equal(200)
store_close(store)
```

</details>

### tax vertical — idempotent replay produces exactly one effect

#### replaying tax_rate_set returns duplicate-key and does not change the rate

- replaying tax_rate_set returns duplicate-key and does not change the rate
- Set 875 bp under key same-key
   - Expected: first.reason equals `accepted`
- Replay the SAME key with a DIFFERENT rate (500) — must not take effect
   - Expected: replay.reason equals `duplicate-key`
- No second effect — rate still 875, outbox unchanged
   - Expected: tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard") equals `875`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying tax_rate_set returns duplicate-key and does not change the rate")
val store = fresh_store("replay")
val t = tenant_a()
val cfo = cfo_a()
val s = session_for(cfo, t)

step("Set 875 bp under key same-key")
val first = tax_rate_set(store, s, t, cfo, envelope("same-key"), "US-CA", "standard", 875)
expect(first.reason).to_equal("accepted")
val outbox_after_first = outbox_pending(store, "tenant-a").len()

step("Replay the SAME key with a DIFFERENT rate (500) — must not take effect")
val replay = tax_rate_set(store, s, t, cfo, envelope("same-key"), "US-CA", "standard", 500)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(reason_allowed(replay.reason)).to_be(true)

step("No second effect — rate still 875, outbox unchanged")
expect(tax_effective_rate_bp(store, "tenant-a", "US-CA", "standard")).to_equal(875)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
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

- Canonical SPipe generation for source `3a438e33f75498529bd7d363d8b75a7cc6a1400a36203dddc2fdf133833b54b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a438e33f75498529bd7d363d8b75a7cc6a1400a36203dddc2fdf133833b54b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a438e33f75498529bd7d363d8b75a7cc6a1400a36203dddc2fdf133833b54b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finance sets 875 bp and tax_for rounds half-up on the minor unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_tax_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '[1000,1000] @ 875 bp = 88+88 = 176, not the aggregate 175' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
