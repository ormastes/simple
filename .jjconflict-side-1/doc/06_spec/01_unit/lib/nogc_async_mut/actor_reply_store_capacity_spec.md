# Actor Reply Store Capacity Specification

> Tests covering ActorScheduler bounded reply reservations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Reply Store Capacity Specification

## Scenarios

### ActorScheduler bounded reply reservations

#### rejects asks before a completed reply would be dropped

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects asks before a completed reply would be dropped
   - Expected: first > 0 is true
   - Expected: second > first is true
   - Expected: replies.allocate_id() equals `-1`
   - Expected: replies.outstanding_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects asks before a completed reply would be dropped")
var replies = ReplyStore.with_capacity(2)
val first = replies.allocate_id()
val second = replies.allocate_id()
expect(first > 0).to_equal(true)
expect(second > first).to_equal(true)
expect(replies.allocate_id()).to_equal(-1)
expect(replies.outstanding_count()).to_equal(2)
```

</details>

#### keeps admission credit through completion until consumption

- keeps admission credit through completion until consumption
   - Expected: replies.put(reply_id, "done") is true
   - Expected: value equals `done`
   - Expected: false is true
   - Expected: replies.allocate_id() equals `-1`
   - Expected: replies.allocate_id() > reply_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps admission credit through completion until consumption")
var replies = ReplyStore.with_capacity(1)
val reply_id = replies.allocate_id()
expect(replies.put(reply_id, "done")).to_equal(true)
if val value = replies.get(reply_id):
    expect(value).to_equal("done")
else:
    expect(false).to_equal(true)
expect(replies.allocate_id()).to_equal(-1)
replies.remove(reply_id)
expect(replies.allocate_id() > reply_id).to_equal(true)
```

</details>

#### cancels an uncompleted reservation without retaining a result

- cancels an uncompleted reservation without retaining a result
   - Expected: replies.has(reply_id) is false
   - Expected: replies.outstanding_count() equals `0`
   - Expected: replies.allocate_id() > reply_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cancels an uncompleted reservation without retaining a result")
var replies = ReplyStore.with_capacity(1)
val reply_id = replies.allocate_id()
replies.cancel(reply_id)
expect(replies.has(reply_id)).to_equal(false)
expect(replies.outstanding_count()).to_equal(0)
expect(replies.allocate_id() > reply_id).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ActorScheduler bounded reply reservations.
- ActorScheduler bounded reply reservations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a85b0b2709ea3d8ec89028e07b3c3c1bb7cd7a043029c13644935aa4c1a426cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a85b0b2709ea3d8ec89028e07b3c3c1bb7cd7a043029c13644935aa4c1a426cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a85b0b2709ea3d8ec89028e07b3c3c1bb7cd7a043029c13644935aa4c1a426cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects asks before a completed reply would be dropped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps admission credit through completion until consumption' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cancels an uncompleted reservation without retaining a result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
