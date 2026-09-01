# Enterprise Pricing / Discounts Vertical — rule config + deterministic price compute

> A sales actor defines a named discount rule (percent_bp or fixed_cents) for a `code` under the durable enterprise store, then pure reads apply the LATEST rule to a base price with EXACT integer minor-unit results (never floats). Every define runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Pricing / Discounts Vertical — rule config + deterministic price compute

A sales actor defines a named discount rule (percent_bp or fixed_cents) for a `code` under the durable enterprise store, then pure reads apply the LATEST rule to a base price with EXACT integer minor-unit results (never floats). Every define runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A sales actor defines a named discount rule (percent_bp or fixed_cents) for a
`code` under the durable enterprise store, then pure reads apply the LATEST rule
to a base price with EXACT integer minor-unit results (never floats). Every
define runs the frozen guarded sequence (session -> rbac -> validation ->
idempotency -> effects in one UoW) and chains a sha256 audit record.

## Rounding rule proven here

Percent discount = `round_half_up(base_cents * value_bp / 10000)` computed on
integers as `(base_cents*value_bp + 5000)/10000`. The boundary case 1000 cents @
875 bp = 87.5 rounds UP to 88; 1000 @ 874 bp = 87.4 rounds DOWN to 87 — the two
adjacent rates straddle the half threshold, proving round-HALF-UP exactly.

## Floor-at-zero clamp proven here

A percent discount of 12000 bp (120%) or a fixed_cents discount larger than the
base never yields a negative price: `price_after_discount` clamps at exactly 0.

## Guarded sequence proven (reproduce-first for each denial)

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | an inactive session cannot define a discount |
| rbac | forbidden | a `viewer` actor cannot define a discount |
| idempotency | duplicate-key | replay returns recorded result, no second effect |

Plus: latest-rule-wins after a second define; unknown-code passthrough; tenant
isolation (tenant-B compute uses only tenant-B rules).

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W21-D).

## Scenarios

### pricing vertical — define a percent discount then compute exact price

#### sales defines 875 bp and price_after_discount rounds half-up on the minor unit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sales defines 875 bp and price_after_discount rounds half-up on the minor unit
- Open a clean store
- Define an 8.75% discount (875 bp) for code SUMMER
   - Expected: set.reason equals `accepted`
- Boundary case: 1000 cents @ 875 bp discount = 87.5 -> rounds UP to 88 -> price 912
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "SUMMER").amount_cents equals `912`
- Exact case: 2000 cents @ 875 bp = 175.0 discount -> price 1825
   - Expected: price_after_discount(store, s, t, rep, usd(2000), "SUMMER").amount_cents equals `1825`
- Currency is preserved on the returned Money
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "SUMMER").currency equals `USD`
- The audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sales defines 875 bp and price_after_discount rounds half-up on the minor unit")
step("Open a clean store")
val store = fresh_store("compute")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)

step("Define an 8.75% discount (875 bp) for code SUMMER")
val set = discount_define(store, s, t, rep, envelope("d-1"), "SUMMER", "percent_bp", 875)
expect(set.reason).to_equal("accepted")
expect(reason_allowed(set.reason)).to_be(true)

step("Boundary case: 1000 cents @ 875 bp discount = 87.5 -> rounds UP to 88 -> price 912")
expect(price_after_discount(store, s, t, rep, usd(1000), "SUMMER").amount_cents).to_equal(912)

step("Exact case: 2000 cents @ 875 bp = 175.0 discount -> price 1825")
expect(price_after_discount(store, s, t, rep, usd(2000), "SUMMER").amount_cents).to_equal(1825)

step("Currency is preserved on the returned Money")
expect(price_after_discount(store, s, t, rep, usd(1000), "SUMMER").currency).to_equal("USD")

step("The audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### pricing vertical — round-half-up boundary is exact

#### reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)

- reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)
- The pure percent-discount helper straddles the half threshold
   - Expected: pricing_percent_discount(1000, 875) equals `88`
   - Expected: pricing_percent_discount(1000, 874) equals `87`
   - Expected: pricing_percent_discount(0, 875) equals `0`
   - Expected: pricing_percent_discount(1000, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)")
step("The pure percent-discount helper straddles the half threshold")
# 1000*875/10000 = 87.5 exactly -> half rounds away from zero -> 88
expect(pricing_percent_discount(1000, 875)).to_equal(88)
# 1000*874/10000 = 87.4 -> below the half -> 87
expect(pricing_percent_discount(1000, 874)).to_equal(87)
# a non-positive base or rate yields 0 discount
expect(pricing_percent_discount(0, 875)).to_equal(0)
expect(pricing_percent_discount(1000, 0)).to_equal(0)
```

</details>

### pricing vertical — fixed_cents discount subtracts a flat amount

#### a 250-cent fixed discount lowers a 1000-cent base to 750

- a 250-cent fixed discount lowers a 1000-cent base to 750
- Define a fixed 250-cent discount for code FLAT
   - Expected: set.reason equals `accepted`
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "FLAT").amount_cents equals `750`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a 250-cent fixed discount lowers a 1000-cent base to 750")
val store = fresh_store("fixed")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
step("Define a fixed 250-cent discount for code FLAT")
val set = discount_define(store, s, t, rep, envelope("d-f"), "FLAT", "fixed_cents", 250)
expect(set.reason).to_equal("accepted")
expect(price_after_discount(store, s, t, rep, usd(1000), "FLAT").amount_cents).to_equal(750)
store_close(store)
```

</details>

### pricing vertical — floor-at-zero clamp (price never goes negative)

#### a percent discount over 100% and an oversized fixed discount both clamp to 0

- a percent discount over 100% and an oversized fixed discount both clamp to 0
- Define a 120% (12000 bp) discount for code MEGA
- 1000 cents @ 12000 bp = 1200 discount, clamped so price = 0 (never -200)
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "MEGA").amount_cents equals `0`
- Define a fixed 5000-cent discount larger than a 1000-cent base
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "OVER").amount_cents equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a percent discount over 100% and an oversized fixed discount both clamp to 0")
val store = fresh_store("clamp")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)

step("Define a 120% (12000 bp) discount for code MEGA")
discount_define(store, s, t, rep, envelope("d-m"), "MEGA", "percent_bp", 12000)
step("1000 cents @ 12000 bp = 1200 discount, clamped so price = 0 (never -200)")
expect(price_after_discount(store, s, t, rep, usd(1000), "MEGA").amount_cents).to_equal(0)

step("Define a fixed 5000-cent discount larger than a 1000-cent base")
discount_define(store, s, t, rep, envelope("d-o"), "OVER", "fixed_cents", 5000)
expect(price_after_discount(store, s, t, rep, usd(1000), "OVER").amount_cents).to_equal(0)
store_close(store)
```

</details>

### pricing vertical — unknown code leaves the base price unchanged

#### price_after_discount for an undefined code returns the base

- price_after_discount for an undefined code returns the base
- No rule was ever defined for NOPE
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "NOPE").amount_cents equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("price_after_discount for an undefined code returns the base")
val store = fresh_store("unknown")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
step("No rule was ever defined for NOPE")
expect(discount_effective(store, "tenant-a", "NOPE").found).to_be(false)
expect(price_after_discount(store, s, t, rep, usd(1000), "NOPE").amount_cents).to_equal(1000)
store_close(store)
```

</details>

### pricing vertical — invalid session is denied

#### reproduce: an inactive session cannot define a discount (invalid-session)

- reproduce: an inactive session cannot define a discount (invalid-session)
- Attempt discount_define with an inactive session
   - Expected: r.reason equals `invalid-session`
- No rule was recorded


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: an inactive session cannot define a discount (invalid-session)")
val store = fresh_store("session")
val t = tenant_a()
val rep = rep_a()
step("Attempt discount_define with an inactive session")
val dead = SessionContext(token: "tok-rep-1", actor_id: "rep-1", tenant_id: "tenant-a", active: false)
val r = discount_define(store, dead, t, rep, envelope("d-s"), "SUMMER", "percent_bp", 500)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-session")
expect(reason_allowed(r.reason)).to_be(true)
step("No rule was recorded")
expect(discount_effective(store, "tenant-a", "SUMMER").found).to_be(false)
store_close(store)
```

</details>

### pricing vertical — rbac denies an unauthorized actor

#### reproduce: a viewer actor cannot define a discount (forbidden)

- reproduce: a viewer actor cannot define a discount (forbidden)
- Attempt discount_define as a viewer role
   - Expected: r.reason equals `forbidden`
- No rule was recorded


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a viewer actor cannot define a discount (forbidden)")
val store = fresh_store("rbac")
val t = tenant_a()
val viewer = viewer_a()
step("Attempt discount_define as a viewer role")
val r = discount_define(store, session_for(viewer, t), t, viewer, envelope("d-x"), "SUMMER", "percent_bp", 500)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(reason_allowed(r.reason)).to_be(true)
step("No rule was recorded")
expect(discount_effective(store, "tenant-a", "SUMMER").found).to_be(false)
store_close(store)
```

</details>

### pricing vertical — invalid record is denied

#### an unknown kind is rejected (invalid-record)

- an unknown kind is rejected (invalid-record)
- Attempt discount_define with an unsupported kind
   - Expected: r.reason equals `invalid-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an unknown kind is rejected (invalid-record)")
val store = fresh_store("invalid")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
step("Attempt discount_define with an unsupported kind")
val r = discount_define(store, s, t, rep, envelope("d-i"), "SUMMER", "bogus", 500)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")
expect(reason_allowed(r.reason)).to_be(true)
store_close(store)
```

</details>

### pricing vertical — latest rule wins (insert-only redefine)

#### a second discount_define supersedes the first for compute

- a second discount_define supersedes the first for compute
- Define 875 bp, then redefine to a fixed 100-cent discount with a fresh key
   - Expected: second.reason equals `accepted`
- Effective rule is the latest (fixed 100); 1000 cents -> price 900
   - Expected: eff.kind equals `fixed_cents`
   - Expected: eff.value equals `100`
   - Expected: price_after_discount(store, s, t, rep, usd(1000), "SUMMER").amount_cents equals `900`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a second discount_define supersedes the first for compute")
val store = fresh_store("latest")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)
step("Define 875 bp, then redefine to a fixed 100-cent discount with a fresh key")
discount_define(store, s, t, rep, envelope("d-first"), "SUMMER", "percent_bp", 875)
val second = discount_define(store, s, t, rep, envelope("d-second"), "SUMMER", "fixed_cents", 100)
expect(second.reason).to_equal("accepted")
step("Effective rule is the latest (fixed 100); 1000 cents -> price 900")
val eff = discount_effective(store, "tenant-a", "SUMMER")
expect(eff.kind).to_equal("fixed_cents")
expect(eff.value).to_equal(100)
expect(price_after_discount(store, s, t, rep, usd(1000), "SUMMER").amount_cents).to_equal(900)
store_close(store)
```

</details>

### pricing vertical — tenant isolation

#### tenant B compute uses only tenant B rules

- tenant B compute uses only tenant B rules
- Tenant A defines 875 bp; tenant B defines 2000 bp for the SAME code
- Each tenant's compute reads only its own rule
   - Expected: discount_effective(store, "tenant-a", "SUMMER").value equals `875`
   - Expected: discount_effective(store, "tenant-b", "SUMMER").value equals `2000`
   - Expected: price_after_discount(store, sa, ta, rep_a_actor, usd(1000), "SUMMER").amount_cents equals `912`
   - Expected: price_after_discount(store, sb, tb, rep_b, usd(1000), "SUMMER").amount_cents equals `800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B compute uses only tenant B rules")
val store = fresh_store("isolation")
val ta = tenant_a()
val rep_a_actor = rep_a()
val sa = session_for(rep_a_actor, ta)
val tb = tenant_b()
val rep_b = ActorContext(actor_id: "rep-b", role: "sales")
val sb = session_for(rep_b, tb)

step("Tenant A defines 875 bp; tenant B defines 2000 bp for the SAME code")
discount_define(store, sa, ta, rep_a_actor, envelope("d-a"), "SUMMER", "percent_bp", 875)
discount_define(store, sb, tb, rep_b, envelope("d-b2"), "SUMMER", "percent_bp", 2000)

step("Each tenant's compute reads only its own rule")
expect(discount_effective(store, "tenant-a", "SUMMER").value).to_equal(875)
expect(discount_effective(store, "tenant-b", "SUMMER").value).to_equal(2000)
# 1000 @ 875 = 88 discount -> 912 for A; 1000 @ 2000 (20%) = 200 -> 800 for B
expect(price_after_discount(store, sa, ta, rep_a_actor, usd(1000), "SUMMER").amount_cents).to_equal(912)
expect(price_after_discount(store, sb, tb, rep_b, usd(1000), "SUMMER").amount_cents).to_equal(800)
store_close(store)
```

</details>

### pricing vertical — idempotent replay produces exactly one effect

#### replaying discount_define returns duplicate-key and does not change the rule

- replaying discount_define returns duplicate-key and does not change the rule
- Define 875 bp under key same-key
   - Expected: first.reason equals `accepted`
- Replay the SAME key with a DIFFERENT rule (500) — must not take effect
   - Expected: replay.reason equals `duplicate-key`
- No second effect — rule still 875 bp, outbox unchanged
   - Expected: discount_effective(store, "tenant-a", "SUMMER").value equals `875`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying discount_define returns duplicate-key and does not change the rule")
val store = fresh_store("replay")
val t = tenant_a()
val rep = rep_a()
val s = session_for(rep, t)

step("Define 875 bp under key same-key")
val first = discount_define(store, s, t, rep, envelope("same-key"), "SUMMER", "percent_bp", 875)
expect(first.reason).to_equal("accepted")
val outbox_after_first = outbox_pending(store, "tenant-a").len()

step("Replay the SAME key with a DIFFERENT rule (500) — must not take effect")
val replay = discount_define(store, s, t, rep, envelope("same-key"), "SUMMER", "percent_bp", 500)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(reason_allowed(replay.reason)).to_be(true)

step("No second effect — rule still 875 bp, outbox unchanged")
expect(discount_effective(store, "tenant-a", "SUMMER").value).to_equal(875)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `664f3c55eec1000299057b9da3ab5806d6f05ea83566ef81bee82883cb9d6d7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `664f3c55eec1000299057b9da3ab5806d6f05ea83566ef81bee82883cb9d6d7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `664f3c55eec1000299057b9da3ab5806d6f05ea83566ef81bee82883cb9d6d7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sales defines 875 bp and price_after_discount rounds half-up on the minor unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: 1000@875 rounds UP (87.5->88) while 1000@874 rounds DOWN (87.4->87)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_pricing_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a 250-cent fixed discount lowers a 1000-cent base to 750' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
