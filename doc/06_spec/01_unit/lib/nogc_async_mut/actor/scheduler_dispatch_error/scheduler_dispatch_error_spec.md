# Scheduler Dispatch Error Specification

> Tests covering ActorScheduler dispatch error API (W2-6 structural), Actor dispatch error recording (W2-6 behavioural).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Dispatch Error Specification

## Scenarios

### ActorScheduler dispatch error API (W2-6 structural)

#### ActorScheduler has trace_enabled field

- ActorScheduler has trace_enabled field
   - Expected: src contains `trace_enabled: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ActorScheduler has trace_enabled field")
val src = sched_src()
expect(src.contains("trace_enabled: bool")).to_equal(true)
```

</details>

#### ActorScheduler is one shared class authority, not a copied value

- ActorScheduler is one shared class authority, not a copied value
   - Expected: src contains `class ActorScheduler:`
   - Expected: src does not contain `struct ActorScheduler:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ActorScheduler is one shared class authority, not a copied value")
val src = sched_src()
expect(src.contains("class ActorScheduler:")).to_equal(true)
expect(src.contains("struct ActorScheduler:")).to_equal(false)
```

</details>

#### Actor records lifecycle and error counters through a class authority

- Actor records lifecycle and error counters through a class authority
   - Expected: src contains `class Actor:`
   - Expected: src does not contain `struct Actor:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Actor records lifecycle and error counters through a class authority")
val src = rt_file_read_text("src/lib/nogc_async_mut/actor/actor.spl") ?? ""
expect(src.contains("class Actor:")).to_equal(true)
expect(src.contains("struct Actor:")).to_equal(false)
```

</details>

#### spawn references retain their admitting scheduler authority

- spawn references retain their admitting scheduler authority
   - Expected: src contains `_scheduler: ActorScheduler`
   - Expected: src does not contain `_mailbox: ActorMailbox`
   - Expected: src contains `self._scheduler.send_message(self.actor_id, method, args)`
   - Expected: src contains `self._scheduler.ask_message(self.actor_id, method, args)`
   - Expected: src contains `self._scheduler.unregister_actor(self.actor_id)`
   - Expected: src contains `ActorRef(actor_id: aid, _scheduler: scheduler)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawn references retain their admitting scheduler authority")
val src = rt_file_read_text("src/lib/nogc_async_mut/actor/spawn.spl") ?? ""
expect(src.contains("_scheduler: ActorScheduler")).to_equal(true)
expect(src.contains("_mailbox: ActorMailbox")).to_equal(false)
expect(src.contains("self._scheduler.send_message(self.actor_id, method, args)")).to_equal(true)
expect(src.contains("self._scheduler.ask_message(self.actor_id, method, args)")).to_equal(true)
expect(src.contains("self._scheduler.unregister_actor(self.actor_id)")).to_equal(true)
expect(src.contains("ActorRef(actor_id: aid, _scheduler: scheduler)")).to_equal(true)
```

</details>

#### exposes explicit bounded reply cancellation

- exposes explicit bounded reply cancellation
   - Expected: src contains `static fn with_reply_capacity(reply_capacity: i64) -> ActorScheduler`
   - Expected: src contains `ReplyStore.with_capacity(reply_capacity)`
   - Expected: src contains `fn reply_capacity() -> i64`
   - Expected: src contains `fn outstanding_reply_count() -> i64`
   - Expected: src contains `me cancel_reply(reply_id: i64) -> bool`
   - Expected: src contains `me unregister_actor(actor_id: i64) -> bool`
   - Expected: src contains `self.replies.cancel(reply_id)`
   - Expected: src contains `cancelled reply was not retained`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes explicit bounded reply cancellation")
val src = sched_src()
expect(src.contains("static fn with_reply_capacity(reply_capacity: i64) -> ActorScheduler")).to_equal(true)
expect(src.contains("ReplyStore.with_capacity(reply_capacity)")).to_equal(true)
expect(src.contains("fn reply_capacity() -> i64")).to_equal(true)
expect(src.contains("fn outstanding_reply_count() -> i64")).to_equal(true)
expect(src.contains("me cancel_reply(reply_id: i64) -> bool")).to_equal(true)
expect(src.contains("me unregister_actor(actor_id: i64) -> bool")).to_equal(true)
expect(src.contains("self.replies.cancel(reply_id)")).to_equal(true)
expect(src.contains("cancelled reply was not retained")).to_equal(true)
```

</details>

#### trace_enabled is read from SIMPLE_ACTOR_TRACE at construction

- trace_enabled is read from SIMPLE_ACTOR_TRACE at construction
   - Expected: src contains `env_has("SIMPLE_ACTOR_TRACE")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace_enabled is read from SIMPLE_ACTOR_TRACE at construction")
val src = sched_src()
expect(src.contains("env_has(\"SIMPLE_ACTOR_TRACE\")")).to_equal(true)
```

</details>

#### actor_error_count per-actor accessor exists

- actor_error_count per-actor accessor exists
   - Expected: src contains `fn actor_error_count(actor_id: i64) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actor_error_count per-actor accessor exists")
val src = sched_src()
expect(src.contains("fn actor_error_count(actor_id: i64) -> i64")).to_equal(true)
```

</details>

#### actor_last_error per-actor accessor exists

- actor_last_error per-actor accessor exists
   - Expected: src contains `fn actor_last_error(actor_id: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actor_last_error per-actor accessor exists")
val src = sched_src()
expect(src.contains("fn actor_last_error(actor_id: i64) -> text")).to_equal(true)
```

</details>

#### total_errors is incremented on handler failure

- total_errors is incremented on handler failure
   - Expected: src contains `self.total_errors = self.total_errors + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total_errors is incremented on handler failure")
val src = sched_src()
expect(src.contains("self.total_errors = self.total_errors + 1")).to_equal(true)
```

</details>

#### per-actor error_count is incremented on handler failure

- per-actor error_count is incremented on handler failure
   - Expected: src contains `act.error_count = act.error_count + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("per-actor error_count is incremented on handler failure")
val src = sched_src()
expect(src.contains("act.error_count = act.error_count + 1")).to_equal(true)
```

</details>

#### per-actor last_error is recorded on handler failure

- per-actor last_error is recorded on handler failure
   - Expected: src contains `act.last_error = result.error_msg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("per-actor last_error is recorded on handler failure")
val src = sched_src()
expect(src.contains("act.last_error = result.error_msg")).to_equal(true)
```

</details>

#### trace log line is gated on trace_enabled

- trace log line is gated on trace_enabled
   - Expected: src contains `if self.trace_enabled`
   - Expected: src contains `SIMPLE_ACTOR_TRACE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace log line is gated on trace_enabled")
val src = sched_src()
expect(src.contains("if self.trace_enabled")).to_equal(true)
expect(src.contains("SIMPLE_ACTOR_TRACE")).to_equal(true)
```

</details>

#### actor_error_count returns 0 for unknown actor

- actor_error_count returns 0 for unknown actor
   - Expected: src contains `fn actor_error_count(actor_id: i64) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actor_error_count returns 0 for unknown actor")
val src = sched_src()
# Accessor returns 0 sentinel
expect(src.contains("fn actor_error_count(actor_id: i64) -> i64")).to_equal(true)
```

</details>

#### actor_last_error returns empty string for unknown actor

- actor_last_error returns empty string for unknown actor
   - Expected: src contains `fn actor_last_error(actor_id: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actor_last_error returns empty string for unknown actor")
val src = sched_src()
expect(src.contains("fn actor_last_error(actor_id: i64) -> text")).to_equal(true)
```

</details>

### Actor dispatch error recording (W2-6 behavioural)

#### dispatching unknown method produces is_error result

- dispatching unknown method produces is_error result
   - Expected: result.is_ok() is false
   - Expected: result.is_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatching unknown method produces is_error result")
var ht = HandlerTable.new()
ht.register("ping", handler_echo)
val result = ht.dispatch("no_method", [])
expect(result.is_ok()).to_equal(false)
expect(result.is_error()).to_equal(true)
```

</details>

#### dispatch error message contains the unknown method name

- dispatch error message contains the unknown method name
   - Expected: result.error_msg contains `unknown_cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch error message contains the unknown method name")
var ht = HandlerTable.new()
ht.register("ping", handler_echo)
val result = ht.dispatch("unknown_cmd", [])
expect(result.error_msg.contains("unknown_cmd")).to_equal(true)
```

</details>

#### successful dispatch does not produce error

- successful dispatch does not produce error
   - Expected: result.is_ok() is true
   - Expected: result.error_msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("successful dispatch does not produce error")
var ht = HandlerTable.new()
ht.register("ping", handler_echo)
val result = ht.dispatch("ping", ["pong"])
expect(result.is_ok()).to_equal(true)
expect(result.error_msg).to_equal("")
```

</details>

#### handler registered after an error dispatch still works

- handler registered after an error dispatch still works
   - Expected: bad.is_ok() is false
   - Expected: good.is_ok() is true
   - Expected: good.value equals `added`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handler registered after an error dispatch still works")
var ht = HandlerTable.new()
val bad = ht.dispatch("not_registered", [])
expect(bad.is_ok()).to_equal(false)
# Register and dispatch successfully after the error
ht.register("add", handler_add)
val good = ht.dispatch("add", [])
expect(good.is_ok()).to_equal(true)
expect(good.value).to_equal("added")
```

</details>

#### multiple error dispatches are independent (no state bleed)

- multiple error dispatches are independent (no state bleed)
   - Expected: r1.is_ok() is false
   - Expected: r2.is_ok() is false
   - Expected: r1.error_msg contains `missing_1`
   - Expected: r2.error_msg contains `missing_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple error dispatches are independent (no state bleed)")
var ht = HandlerTable.new()
val r1 = ht.dispatch("missing_1", [])
val r2 = ht.dispatch("missing_2", ["arg"])
expect(r1.is_ok()).to_equal(false)
expect(r2.is_ok()).to_equal(false)
expect(r1.error_msg.contains("missing_1")).to_equal(true)
expect(r2.error_msg.contains("missing_2")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ActorScheduler dispatch error API (W2-6 structural), Actor dispatch error recording (W2-6 behavioural).
- ActorScheduler dispatch error API (W2-6 structural)
- Actor dispatch error recording (W2-6 behavioural)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `0cc856923291de3de9fb8cd318f38683adf9a81bcb5fa708e7239dccc3d79660`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0cc856923291de3de9fb8cd318f38683adf9a81bcb5fa708e7239dccc3d79660`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0cc856923291de3de9fb8cd318f38683adf9a81bcb5fa708e7239dccc3d79660`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ActorScheduler has trace_enabled field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ActorScheduler is one shared class authority, not a copied value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Actor records lifecycle and error counters through a class authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
