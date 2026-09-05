# Actor Mailbox Close Specification

> Tests covering ActorMailbox shared close admission, ActorRef scheduler-owned admission and close.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Mailbox Close Specification

## Scenarios

### ActorMailbox shared close admission

#### rejects new sends after close but drains accepted FIFO work

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects new sends after close but drains accepted FIFO work


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects new sends after close but drains accepted FIFO work")
val mailbox = ActorMailbox.new(2)
val first = ActorMessage.fire_and_forget("first", [])
val second = ActorMessage.fire_and_forget("second", [])
assert_true(mailbox.enqueue(first))
mailbox.close()
assert_true(mailbox.is_closed())
assert_false(mailbox.enqueue(second))
val drained = mailbox.dequeue()
if val message = drained:
    assert_equal(message.method, "first")
else:
    assert_true(false)
assert_true(mailbox.dequeue() == nil)
```

</details>

#### shares close state across copied mailbox handles

- shares close state across copied mailbox handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares close state across copied mailbox handles")
val original = ActorMailbox.new(1)
val copied = original
copied.close()
assert_true(original.is_closed())
assert_false(original.enqueue(ActorMessage.fire_and_forget("late", [])))
```

</details>

#### retains a bounded high-water mark after draining

- retains a bounded high-water mark after draining


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains a bounded high-water mark after draining")
val mailbox = ActorMailbox.new(2)
assert_equal(mailbox.pending_high_water_count(), 0)
assert_true(mailbox.enqueue(ActorMessage.fire_and_forget("one", [])))
assert_true(mailbox.enqueue(ActorMessage.fire_and_forget("two", [])))
assert_false(mailbox.enqueue(ActorMessage.fire_and_forget("three", [])))
assert_equal(mailbox.len(), 2)
assert_true(mailbox.is_full())
assert_equal(mailbox.pending_high_water_count(), 2)
assert_true(mailbox.dequeue() != nil)
assert_equal(mailbox.len(), 1)
assert_equal(mailbox.pending_high_water_count(), 2)
```

</details>

### ActorRef scheduler-owned admission and close

#### routes copied references through one bounded scheduler authority

- routes copied references through one bounded scheduler authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes copied references through one bounded scheduler authority")
val scheduler = ActorScheduler.new()
val original = actor_ref_with_capacity(scheduler, 1)
val copied = original
assert_true(original.send("echo", ["first"]))
assert_false(copied.send("echo", ["full"]))
assert_true(original.has_messages())
scheduler.run_until_idle()
assert_false(copied.has_messages())
```

</details>

#### rejects send and ask through every copied reference after stop

- rejects send and ask through every copied reference after stop


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects send and ask through every copied reference after stop")
val scheduler = ActorScheduler.new()
val original = actor_ref_with_capacity(scheduler, 2)
val copied = original
assert_true(original.send("echo", ["accepted-before-stop"]))
assert_true(copied.stop())
assert_false(original.send("echo", ["late"]))
assert_equal(copied.ask("echo", ["late-ask"]), -1)
assert_false(original.has_messages())
assert_equal(scheduler.outstanding_reply_count(), 0)
assert_false(original.stop())
```

</details>

#### retains an admission-time copy of caller arguments

- retains an admission-time copy of caller arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains an admission-time copy of caller arguments")
val scheduler = ActorScheduler.new()
val actor_ref = actor_ref_with_capacity(scheduler, 1)
var args = ["before"]
val reply_id = actor_ref.ask("echo", args)
assert_true(reply_id > 0)
args[0] = "after"
scheduler.run_until_idle()
if val reply = scheduler.consume_reply(reply_id):
    assert_equal(reply, "before")
else:
    assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ActorMailbox shared close admission, ActorRef scheduler-owned admission and close.
- ActorMailbox shared close admission
- ActorRef scheduler-owned admission and close

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6ccc9ee8a4e1c6e5d1a09c9ab7a0c7e66dd0f9d90ae3d675ad73d2db7ac2cc84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ccc9ee8a4e1c6e5d1a09c9ab7a0c7e66dd0f9d90ae3d675ad73d2db7ac2cc84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ccc9ee8a4e1c6e5d1a09c9ab7a0c7e66dd0f9d90ae3d675ad73d2db7ac2cc84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects new sends after close but drains accepted FIFO work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shares close state across copied mailbox handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains a bounded high-water mark after draining' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
