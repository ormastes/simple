# Enterprise Throttle — bounded state under an identity-cycling flood

> `throttle_admit` records one insert-only counter row per admitted request and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Throttle — bounded state under an identity-cycling flood

`throttle_admit` records one insert-only counter row per admitted request and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## What this fences

`throttle_admit` records one insert-only counter row per admitted request and
scans the counter table linearly on every attempt. `throttle_prune` reclaims
rows, but ONLY when every retained row belongs to a window strictly older than
the live one — so within a SINGLE live window it never fires. That leaves a
residual DoS surface (the "throttle linear scan" residual in
`doc/07_guide/app/enterprise/security_posture.md`): an attacker who cycles
through many DISTINCT identities inside one window inflates the counter table
without bound. Two attacker wins follow from the same unbounded structure:

  (a) MEMORY — retained rows grow linearly with the number of distinct
      identities seen in the live window; nothing evicts them until the window
      turns.
  (b) CPU — every subsequent attempt's `throttle_count` / `throttle_prune`
      scan is linear in that same growing table, so the defence gets more
      expensive to run the harder it is flooded.

The oracle for boundedness is `throttle_rows_retained`: the absolute count of
counter rows the table holds right now, across every key. This spec floods the
throttle with far more distinct identities than the ceiling within one window
and asserts the retained set stays at or below the fixed ceiling
`throttle_max_rows()`. Before the W15-A fix the table held one row per distinct
identity (retained == flood size, well over the ceiling) and this FAILED. The
fix bounds the table with a fail-closed capacity ceiling: once the live window
is full and cannot be pruned, a genuinely NEW identity is denied rather than
inserted — memory is capped and no already-tracked key's lockout is weakened.

The companion `enterprise_auth_throttle_spec.spl` proves the externally
observable throttle behaviour is UNCHANGED (same lockout after the same
threshold within the window); this spec proves only that the state is now
bounded.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (v2, W15-A).

## Scenarios

### enterprise throttle — state stays bounded under an identity flood

#### retains at most the fixed ceiling of counter rows across many distinct identities in one window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains at most the fixed ceiling of counter rows across many distinct identities in one window
- The ceiling is a fixed, positive constant naming the memory bound
- Flood the SAME live window (now=1000, window_secs=60) with ceiling+200 distinct identities
- Retained counter rows never exceed the ceiling — memory is bounded


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retains at most the fixed ceiling of counter rows across many distinct identities in one window")
val store = fresh("flood")

step("The ceiling is a fixed, positive constant naming the memory bound")
val ceiling = throttle_max_rows()
expect(ceiling > 0).to_be(true)

step("Flood the SAME live window (now=1000, window_secs=60) with ceiling+200 distinct identities")
# Every identity is unique, so each request is the first for its key and
# would be admitted by the per-key limit; only the global capacity
# ceiling can hold the table down. The window label (1000/60 = 16) is
# constant for every call, so throttle_prune can never fire here.
val flood = ceiling + 200
var i = 0
while i < flood:
    throttle_admit(store, "tenant-a|attacker-{i}", 1000, 60, 5)
    i = i + 1

step("Retained counter rows never exceed the ceiling — memory is bounded")
val retained = throttle_rows_retained(store)
# Before the fix this equalled `flood` (one row per distinct identity),
# blowing past the ceiling. The bounded structure caps it.
expect(retained <= ceiling).to_be(true)
# And the bound is actually being exercised: the flood really did try to
# push past the ceiling, so a trivially-empty table is not a false pass.
expect(flood > ceiling).to_be(true)

store_close(store)
```

</details>

#### an already-tracked victim key is still throttled after the table saturates

- an already-tracked victim key is still throttled after the table saturates
- Victim exhausts its 5-request login limit at now=2000 (window 33)
- Saturate the table with a distinct-identity flood in the same window
- The victim's 6th attempt is still denied — its lockout survived saturation
- And the table is still bounded


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("an already-tracked victim key is still throttled after the table saturates")
# Boundedness must not come from silently dropping a real attacker's
# accumulating count. Fill the victim key to its limit FIRST (so its
# rows are the oldest), THEN saturate the table with a distinct-identity
# flood, and confirm the victim is still locked out — proving the cap is
# fail-closed on new identities, not eviction of existing lockouts.
val store = fresh("victim")
val ceiling = throttle_max_rows()

step("Victim exhausts its 5-request login limit at now=2000 (window 33)")
var v = 0
while v < 5:
    throttle_admit(store, "tenant-a|victim", 2000, 60, 5)
    v = v + 1

step("Saturate the table with a distinct-identity flood in the same window")
var i = 0
while i < ceiling + 100:
    throttle_admit(store, "tenant-a|flood-{i}", 2000, 60, 5)
    i = i + 1

step("The victim's 6th attempt is still denied — its lockout survived saturation")
val victim_again = throttle_admit(store, "tenant-a|victim", 2000, 60, 5)
expect(victim_again).to_be(false)

step("And the table is still bounded")
expect(throttle_rows_retained(store) <= ceiling).to_be(true)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0940e92682e4b3421504f7a290cdc0ebf521f8f48e96f9e0f610982317ef9ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0940e92682e4b3421504f7a290cdc0ebf521f8f48e96f9e0f610982317ef9ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0940e92682e4b3421504f7a290cdc0ebf521f8f48e96f9e0f610982317ef9ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.spl
mirror: doc/06_spec/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains at most the fixed ceiling of counter rows across many distinct identities in one window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/enterprise/enterprise_auth_throttle_bound_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an already-tracked victim key is still throttled after the table saturates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
