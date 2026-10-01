# Multi-Currency / FX Vertical — guarded rate-set + deterministic conversion

> The FX flow of the Simple Enterprise Suite (lane W20-C) against the durable enterprise store: the finance role records currency conversion rates (insert-only, micro-unit integer ratios), and a pure read converts `Money` between currencies using the LATEST rate with a float-free round-half-up rule.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-Currency / FX Vertical — guarded rate-set + deterministic conversion

The FX flow of the Simple Enterprise Suite (lane W20-C) against the durable enterprise store: the finance role records currency conversion rates (insert-only, micro-unit integer ratios), and a pure read converts `Money` between currencies using the LATEST rate with a float-free round-half-up rule.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md (W20-C) |
| Design | src/lib/nogc_sync_mut/enterprise_fx/fx.spl |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The FX flow of the Simple Enterprise Suite (lane W20-C) against the durable
enterprise store: the finance role records currency conversion rates
(insert-only, micro-unit integer ratios), and a pure read converts `Money`
between currencies using the LATEST rate with a float-free round-half-up rule.

## Convert contract proven here

- `fx_convert(store, session, amount, to_currency)` returns Money in
  `to_currency`; converted_cents = round_half_up(amount_cents * rate_micro / 1e6),
  computed in i64 integer math (never floats).
- EXACT amounts asserted, including a round-half-up boundary (949.5 -> 950).
- Identity: converting a currency to itself returns the same amount.
- Latest-rate-wins: a later inserted rate supersedes an earlier one.

## Guarded sequence proven here (reproduce-first for guards + boundary)

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session   | invalid-session | cross-tenant / inactive session rejected |
| rbac      | forbidden       | a sales-role actor cannot set a rate |
| validation| invalid-record  | empty / same-currency / non-positive rate |
| idempotency| duplicate-key  | replay returns recorded result, one rate row |
| convert   | not-found       | conversion with no rate is denied (closed set) |

## Invariants

- rates are insert-only; the effective rate is the latest by a pure fold.
- every rate-set appends a sha256-chained audit row (verified end to end).
- tenant B sees none of tenant A's rates and cannot mutate them.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md (W20-C)
**Design:** src/lib/nogc_sync_mut/enterprise_fx/fx.spl

Lane: .spipe/simple_enterprise_suite (W20-C).

## Scenarios

### fx vertical — set a rate then convert known amounts (exact integer math)

#### converts USD->EUR at 0.90 with exact minor-unit results and a round-half-up boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts USD->EUR at 0.90 with exact minor-unit results and a round-half-up boundary
- Finance records USD->EUR = 0.90 (micro 900000)
   - Expected: fx_rate_set(store, sf, t, fin, envelope("convert-r"), "USD", "EUR", 900_000).reason equals `accepted`
   - Expected: fx_latest_rate_micro(store, "tenant-a", "USD", "EUR") equals `900_000`
- 1000 USD-cents * 0.90 = 900 EUR-cents exactly
   - Expected: got.amount_cents equals `900`
   - Expected: got.currency equals `EUR`
- Boundary: 1055 * 0.90 = 949.5 -> round-half-up -> 950
   - Expected: boundary.amount_cents equals `950`
   - Expected: boundary.currency equals `EUR`
- Just below boundary: 1054 * 0.90 = 948.6 -> 949
   - Expected: fx_convert(store, sf, Money(amount_cents: 1054, currency: "USD"), "EUR").amount_cents equals `949`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts USD->EUR at 0.90 with exact minor-unit results and a round-half-up boundary")
step("Finance records USD->EUR = 0.90 (micro 900000)")
val store = fresh_store("convert")
val t = tenant_a()
val fin = finance_a()
val sf = session_for(fin, t)
expect(fx_rate_set(store, sf, t, fin, envelope("convert-r"), "USD", "EUR", 900_000).reason).to_equal("accepted")
expect(fx_latest_rate_micro(store, "tenant-a", "USD", "EUR")).to_equal(900_000)

step("1000 USD-cents * 0.90 = 900 EUR-cents exactly")
val got = fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "EUR")
expect(got.amount_cents).to_equal(900)
expect(got.currency).to_equal("EUR")

step("Boundary: 1055 * 0.90 = 949.5 -> round-half-up -> 950")
val boundary = fx_convert(store, sf, Money(amount_cents: 1055, currency: "USD"), "EUR")
expect(boundary.amount_cents).to_equal(950)
expect(boundary.currency).to_equal("EUR")

step("Just below boundary: 1054 * 0.90 = 948.6 -> 949")
expect(fx_convert(store, sf, Money(amount_cents: 1054, currency: "USD"), "EUR").amount_cents).to_equal(949)

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### self-conversion is the identity — same amount, same currency, no rate needed

- self-conversion is the identity — same amount, same currency, no rate needed
- Convert USD to USD without any rate present — amount is unchanged
   - Expected: same.amount_cents equals `4242`
   - Expected: same.currency equals `USD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("self-conversion is the identity — same amount, same currency, no rate needed")
val store = fresh_store("identity")
val sf = session_for(finance_a(), tenant_a())
step("Convert USD to USD without any rate present — amount is unchanged")
val same = fx_convert(store, sf, Money(amount_cents: 4242, currency: "USD"), "USD")
expect(same.amount_cents).to_equal(4242)
expect(same.currency).to_equal("USD")
store_close(store)
```

</details>

#### latest rate wins — a later insert supersedes the earlier one

- latest rate wins — a later insert supersedes the earlier one
- 1000 USD at the seeded 0.90 -> 900 EUR
   - Expected: fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "EUR").amount_cents equals `900`
- Finance records a NEW USD->EUR = 0.95 (micro 950000)
   - Expected: fx_rate_set(store, sf, t, fin, envelope("latest-r2"), "USD", "EUR", 950_000).reason equals `accepted`
   - Expected: fx_latest_rate_micro(store, "tenant-a", "USD", "EUR") equals `950_000`
- Now 1000 USD converts at the latest 0.95 -> 950 EUR
   - Expected: fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "EUR").amount_cents equals `950`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("latest rate wins — a later insert supersedes the earlier one")
val store = seed_usd_eur("latest")
val t = tenant_a()
val fin = finance_a()
val sf = session_for(fin, t)
step("1000 USD at the seeded 0.90 -> 900 EUR")
expect(fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "EUR").amount_cents).to_equal(900)
step("Finance records a NEW USD->EUR = 0.95 (micro 950000)")
expect(fx_rate_set(store, sf, t, fin, envelope("latest-r2"), "USD", "EUR", 950_000).reason).to_equal("accepted")
expect(fx_latest_rate_micro(store, "tenant-a", "USD", "EUR")).to_equal(950_000)
step("Now 1000 USD converts at the latest 0.95 -> 950 EUR")
expect(fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "EUR").amount_cents).to_equal(950)
store_close(store)
```

</details>

### fx vertical — guarded denials (reproduce-first)

#### denies an unauthorized actor at the rbac rung and leaves the ledger untouched

- denies an unauthorized actor at the rbac rung and leaves the ledger untouched
- A sales-role actor attempts a rate-set — the rbac rung fires 'forbidden'
   - Expected: r.reason equals `forbidden`
- An inactive session is rejected before rbac
   - Expected: fx_rate_set(store, dead, t, finance_a(), envelope("rbac-dead"), "USD", "EUR", 900_000).reason equals `invalid-session`
- Same-currency and non-positive rates are invalid-record
   - Expected: fx_rate_set(store, sf, t, fin, envelope("rbac-same"), "USD", "USD", 900_000).reason equals `invalid-record`
   - Expected: fx_rate_set(store, sf, t, fin, envelope("rbac-zero"), "USD", "EUR", 0).reason equals `invalid-record`
- No rate was recorded by any denial
   - Expected: fx_latest_rate_micro(store, "tenant-a", "USD", "EUR") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies an unauthorized actor at the rbac rung and leaves the ledger untouched")
val store = fresh_store("rbac")
val t = tenant_a()
step("A sales-role actor attempts a rate-set — the rbac rung fires 'forbidden'")
val clerk = ActorContext(actor_id: "clerk-1", role: "sales")
val r = fx_rate_set(store, session_for(clerk, t), t, clerk, envelope("rbac-r"), "USD", "EUR", 900_000)
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(reason_allowed(r.reason)).to_be(true)
step("An inactive session is rejected before rbac")
var dead = session_for(finance_a(), t)
dead.active = false
expect(fx_rate_set(store, dead, t, finance_a(), envelope("rbac-dead"), "USD", "EUR", 900_000).reason).to_equal("invalid-session")
step("Same-currency and non-positive rates are invalid-record")
val fin = finance_a()
val sf = session_for(fin, t)
expect(fx_rate_set(store, sf, t, fin, envelope("rbac-same"), "USD", "USD", 900_000).reason).to_equal("invalid-record")
expect(fx_rate_set(store, sf, t, fin, envelope("rbac-zero"), "USD", "EUR", 0).reason).to_equal("invalid-record")
step("No rate was recorded by any denial")
expect(fx_latest_rate_micro(store, "tenant-a", "USD", "EUR")).to_equal(-1)
store_close(store)
```

</details>

#### denies a conversion with no rate using the closed-set reason not-found

- denies a conversion with no rate using the closed-set reason not-found
- No USD->GBP rate exists — fx_convert returns the -1 sentinel
   - Expected: fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "GBP").amount_cents equals `-1`
- fx_convert_result denies with a closed-set reason (not-found)
   - Expected: r.reason equals `not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies a conversion with no rate using the closed-set reason not-found")
val store = fresh_store("missing")
val t = tenant_a()
val fin = finance_a()
val sf = session_for(fin, t)
step("No USD->GBP rate exists — fx_convert returns the -1 sentinel")
expect(fx_convert(store, sf, Money(amount_cents: 1000, currency: "USD"), "GBP").amount_cents).to_equal(-1)
step("fx_convert_result denies with a closed-set reason (not-found)")
val r = fx_convert_result(store, sf, t, fin, Money(amount_cents: 1000, currency: "USD"), "GBP")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("not-found")
expect(reason_allowed(r.reason)).to_be(true)
store_close(store)
```

</details>

### fx vertical — idempotent replay produces exactly one effect

#### replaying the same rate-set command records only one rate row

- replaying the same rate-set command records only one rate row
- Set USD->EUR once with a fixed key
   - Expected: fx_rate_set(store, sf, t, fin, envelope("same-key"), "USD", "EUR", 900_000).reason equals `accepted`
- Replay the SAME idempotency key with a DIFFERENT rate value
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `USD->EUR`
- No second effect — the latest rate is still the first one, outbox unchanged
   - Expected: fx_latest_rate_micro(store, "tenant-a", "USD", "EUR") equals `900_000`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying the same rate-set command records only one rate row")
val store = fresh_store("replay")
val t = tenant_a()
val fin = finance_a()
val sf = session_for(fin, t)
step("Set USD->EUR once with a fixed key")
expect(fx_rate_set(store, sf, t, fin, envelope("same-key"), "USD", "EUR", 900_000).reason).to_equal("accepted")
val outbox_after = outbox_pending(store, "tenant-a").len()
step("Replay the SAME idempotency key with a DIFFERENT rate value")
val replay = fx_rate_set(store, sf, t, fin, envelope("same-key"), "USD", "EUR", 111_111)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("USD->EUR")
step("No second effect — the latest rate is still the first one, outbox unchanged")
expect(fx_latest_rate_micro(store, "tenant-a", "USD", "EUR")).to_equal(900_000)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after)
store_close(store)
```

</details>

### fx vertical — tenant isolation

#### tenant B sees none of tenant A's rates and converts as not-found

- tenant B sees none of tenant A's rates and converts as not-found
- Tenant B has no USD->EUR rate of its own
   - Expected: fx_latest_rate_micro(store, "tenant-b", "USD", "EUR") equals `-1`
- A tenant-B conversion finds no rate (not-found), unaffected by tenant A's 0.90
   - Expected: fx_convert(store, sbb, Money(amount_cents: 1000, currency: "USD"), "EUR").amount_cents equals `-1`
   - Expected: fx_convert_result(store, sbb, tb, fin_b, Money(amount_cents: 1000, currency: "USD"), "EUR").reason equals `not-found`
- A cross-tenant session (tenant-B session against tenant-A context) is rejected outright
   - Expected: fx_rate_set(store, sbb, ta, fin_b, envelope("iso-x"), "USD", "EUR", 800_000).reason equals `invalid-session`
- Tenant A's rate is untouched
   - Expected: fx_latest_rate_micro(store, "tenant-a", "USD", "EUR") equals `900_000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B sees none of tenant A's rates and converts as not-found")
val store = seed_usd_eur("isolation")
step("Tenant B has no USD->EUR rate of its own")
expect(fx_latest_rate_micro(store, "tenant-b", "USD", "EUR")).to_equal(-1)
val tb = tenant_b()
val fin_b = ActorContext(actor_id: "fin-b", role: "finance")
val sbb = session_for(fin_b, tb)
step("A tenant-B conversion finds no rate (not-found), unaffected by tenant A's 0.90")
expect(fx_convert(store, sbb, Money(amount_cents: 1000, currency: "USD"), "EUR").amount_cents).to_equal(-1)
expect(fx_convert_result(store, sbb, tb, fin_b, Money(amount_cents: 1000, currency: "USD"), "EUR").reason).to_equal("not-found")
step("A cross-tenant session (tenant-B session against tenant-A context) is rejected outright")
val ta = tenant_a()
expect(fx_rate_set(store, sbb, ta, fin_b, envelope("iso-x"), "USD", "EUR", 800_000).reason).to_equal("invalid-session")
step("Tenant A's rate is untouched")
expect(fx_latest_rate_micro(store, "tenant-a", "USD", "EUR")).to_equal(900_000)
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

- **Plan:** `.spipe/simple_enterprise_suite/state.md (W20-C)`
- **Design:** `src/lib/nogc_sync_mut/enterprise_fx/fx.spl`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b773b79e10d8abb45043cc94cec19d90343305b87793dd467ceb25efa915578`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b773b79e10d8abb45043cc94cec19d90343305b87793dd467ceb25efa915578`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b773b79e10d8abb45043cc94cec19d90343305b87793dd467ceb25efa915578`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts USD->EUR at 0.90 with exact minor-unit results and a round-half-up boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'self-conversion is the identity — same amount, same currency, no rate needed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_fx_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'latest rate wins — a later insert supersedes the earlier one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
