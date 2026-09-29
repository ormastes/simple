# Actor Scheduler Ready Queue Specification

> Tests covering ActorScheduler owner-thread admission guard, ActorScheduler ready-queue cursor compaction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Scheduler Ready Queue Specification

## Scenarios

### ActorScheduler owner-thread admission guard

#### admits only the exact positive scheduler thread identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits only the exact positive scheduler thread identity
   - Expected: actor_scheduler_thread_domain_allows(41, 41) is true
   - Expected: actor_scheduler_thread_domain_allows(41, 42) is false
   - Expected: actor_scheduler_thread_domain_allows(0, 0) is false
   - Expected: actor_scheduler_thread_domain_allows(-1, -1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits only the exact positive scheduler thread identity")
expect(actor_scheduler_thread_domain_allows(41, 41)).to_equal(true)
expect(actor_scheduler_thread_domain_allows(41, 42)).to_equal(false)
expect(actor_scheduler_thread_domain_allows(0, 0)).to_equal(false)
expect(actor_scheduler_thread_domain_allows(-1, -1)).to_equal(false)
```

</details>

#### fails closed for reply lifecycle and scheduler queries outside the owner domain

- fails closed for reply lifecycle and scheduler queries outside the owner domain
   - Expected: scheduler.send_message(actor_id, "missing", []) is true
   - Expected: scheduler.send_message(actor_id, "echo", ["pending"]) is true
   - Expected: scheduler.outstanding_reply_count() equals `1`
   - Expected: completed equals `completed`
   - Expected: scheduler.actor_count() equals `1`
   - Expected: scheduler.pending_message_count() equals `1`
   - Expected: scheduler.actor_error_count(actor_id) equals `1`
   - Expected: scheduler.actor_last_error(actor_id) equals `method not found: missing`
   - Expected: scheduler.reply_capacity() equals `0`
   - Expected: scheduler.outstanding_reply_count() equals `0`
   - Expected: scheduler.cancel_reply(reply_id) is false
   - Expected: scheduler.actor_count() equals `0`
   - Expected: scheduler.pending_message_count() equals `0`
   - Expected: scheduler.actor_error_count(actor_id) equals `0`
   - Expected: scheduler.actor_last_error(actor_id) equals ``
   - Expected: scheduler.stats_string() equals `Scheduler(unavailable: wrong thread)`
   - Expected: scheduler.outstanding_reply_count() equals `1`
   - Expected: completed equals `completed`
   - Expected: scheduler.actor_count() equals `1`
   - Expected: scheduler.pending_message_count() equals `1`
   - Expected: scheduler.actor_error_count(actor_id) equals `1`
   - Expected: scheduler.actor_last_error(actor_id) equals `method not found: missing`
   - Expected: scheduler.cancel_reply(reply_id) is true
   - Expected: scheduler.outstanding_reply_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed for reply lifecycle and scheduler queries outside the owner domain")
val scheduler = ActorScheduler.with_reply_capacity(2)
var handlers = HandlerTable.new()
handlers.register("echo", actor_owner_guard_echo)
val actor_id = scheduler.register_actor(Actor.new(handlers))
val reply_id = scheduler.ask_message(actor_id, "echo", ["completed"])
scheduler.run_until_idle()
expect(scheduler.send_message(actor_id, "missing", [])).to_equal(true)
scheduler.run_once()
expect(scheduler.send_message(actor_id, "echo", ["pending"])).to_equal(true)
val owner_thread_id = scheduler.owner_thread_id
expect(reply_id).to_be_greater_than(0)
expect(scheduler.outstanding_reply_count()).to_equal(1)
if val completed = scheduler.get_reply(reply_id):
    expect(completed).to_equal("completed")
else:
    fail("completed reply must be observable in the owner domain")
expect(scheduler.actor_count()).to_equal(1)
expect(scheduler.pending_message_count()).to_equal(1)
expect(scheduler.actor_error_count(actor_id)).to_equal(1)
expect(scheduler.actor_last_error(actor_id)).to_equal("method not found: missing")

scheduler.owner_thread_id = -1
expect(scheduler.get_reply(reply_id)).to_be_nil()
expect(scheduler.reply_capacity()).to_equal(0)
expect(scheduler.outstanding_reply_count()).to_equal(0)
expect(scheduler.consume_reply(reply_id)).to_be_nil()
expect(scheduler.cancel_reply(reply_id)).to_equal(false)
expect(scheduler.actor_count()).to_equal(0)
expect(scheduler.pending_message_count()).to_equal(0)
expect(scheduler.actor_error_count(actor_id)).to_equal(0)
expect(scheduler.actor_last_error(actor_id)).to_equal("")
expect(scheduler.stats_string()).to_equal("Scheduler(unavailable: wrong thread)")

scheduler.owner_thread_id = owner_thread_id
expect(scheduler.outstanding_reply_count()).to_equal(1)
if val completed = scheduler.get_reply(reply_id):
    expect(completed).to_equal("completed")
else:
    fail("rejected off-domain access must preserve the completed reply")
expect(scheduler.actor_count()).to_equal(1)
expect(scheduler.pending_message_count()).to_equal(1)
expect(scheduler.actor_error_count(actor_id)).to_equal(1)
expect(scheduler.actor_last_error(actor_id)).to_equal("method not found: missing")
expect(scheduler.cancel_reply(reply_id)).to_equal(true)
expect(scheduler.outstanding_reply_count()).to_equal(0)
```

</details>

### ActorScheduler ready-queue cursor compaction

#### does not compact an empty or tiny active queue on every dispatch

- does not compact an empty or tiny active queue on every dispatch
   - Expected: actor_scheduler_ready_queue_should_compact(0, 2) is false
   - Expected: actor_scheduler_ready_queue_should_compact(1, 2) is false
   - Expected: actor_scheduler_ready_queue_should_compact(63, 126) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not compact an empty or tiny active queue on every dispatch")
expect(actor_scheduler_ready_queue_should_compact(0, 2)).to_equal(false)
expect(actor_scheduler_ready_queue_should_compact(1, 2)).to_equal(false)
expect(actor_scheduler_ready_queue_should_compact(63, 126)).to_equal(false)
```

</details>

#### reclaims a fully consumed queue immediately

- reclaims a fully consumed queue immediately
   - Expected: actor_scheduler_ready_queue_should_compact(2, 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reclaims a fully consumed queue immediately")
expect(actor_scheduler_ready_queue_should_compact(2, 2)).to_equal(true)
```

</details>

#### reclaims a half-consumed large queue at the bounded threshold

- reclaims a half-consumed large queue at the bounded threshold
   - Expected: actor_scheduler_ready_queue_should_compact(64, 128) is true
   - Expected: actor_scheduler_ready_queue_should_compact(65, 129) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reclaims a half-consumed large queue at the bounded threshold")
expect(actor_scheduler_ready_queue_should_compact(64, 128)).to_equal(true)
expect(actor_scheduler_ready_queue_should_compact(65, 129)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ActorScheduler owner-thread admission guard, ActorScheduler ready-queue cursor compaction.
- ActorScheduler owner-thread admission guard
- ActorScheduler ready-queue cursor compaction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `7fcd0c814b829dad3f9a4f2c43be940b65b819d88bb1dad954e26642d141de13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7fcd0c814b829dad3f9a4f2c43be940b65b819d88bb1dad954e26642d141de13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7fcd0c814b829dad3f9a4f2c43be940b65b819d88bb1dad954e26642d141de13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only the exact positive scheduler thread identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for reply lifecycle and scheduler queries outside the owner domain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_scheduler_ready_queue_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not compact an empty or tiny active queue on every dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
