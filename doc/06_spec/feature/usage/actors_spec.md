# Actor Model Concurrency

> The actor model provides a message-passing concurrency primitive where isolated actors communicate exclusively through asynchronous messages. Each actor encapsulates its own state and processes messages sequentially from a mailbox, eliminating shared-state races. This spec validates the actor creation, message dispatch, and concurrent execution semantics of Simple's actor system.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Model Concurrency

The actor model provides a message-passing concurrency primitive where isolated actors communicate exclusively through asynchronous messages. Each actor encapsulates its own state and processes messages sequentially from a mailbox, eliminating shared-state races. This spec validates the actor creation, message dispatch, and concurrent execution semantics of Simple's actor system.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RUNTIME-010 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/actors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The actor model provides a message-passing concurrency primitive where isolated actors
communicate exclusively through asynchronous messages. Each actor encapsulates its own
state and processes messages sequentially from a mailbox, eliminating shared-state races.
This spec validates the actor creation, message dispatch, and concurrent execution
semantics of Simple's actor system.

## Syntax

```simple
# Actor message passing (planned)
use std.spec.step

val counter = spawn CounterActor(initial: 0)
counter.send(Increment(by: 1))
val result = counter.ask(GetCount())
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Actor | An isolated concurrent entity with private state and a mailbox |
| Message Passing | Communication via asynchronous send/ask rather than shared memory |
| Mailbox | A queue of incoming messages processed sequentially by the actor |
| Spawn | Creating a new actor instance that runs concurrently |

## Scenarios

### Actors

#### delivers messages in FIFO order through the mailbox

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create a mailbox and enqueue two fire-and-forget messages
   - Expected: mb.enqueue(ActorMessage.fire_and_forget("first", [])) is true
   - Expected: mb.enqueue(ActorMessage.fire_and_forget("second", [])) is true
- drain the mailbox
   - Expected: first?.method equals `first`
   - Expected: second?.method equals `second`
   - Expected: mb.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("create a mailbox and enqueue two fire-and-forget messages")
val mb = ActorMailbox.new(8)
expect(mb.enqueue(ActorMessage.fire_and_forget("first", []))).to_equal(true)
expect(mb.enqueue(ActorMessage.fire_and_forget("second", []))).to_equal(true)
step("drain the mailbox")
val first = mb.dequeue()
val second = mb.dequeue()
# oracle: actor mailboxes must preserve send order (sequential processing)
expect(first?.method).to_equal("first")
expect(second?.method).to_equal("second")
expect(mb.len()).to_equal(0)
```

</details>

#### rejects messages beyond the finite mailbox capacity

- create a one-slot mailbox and fill it
   - Expected: mb.enqueue(ActorMessage.fire_and_forget("only", [])) is true
- attempt to exceed capacity
   - Expected: mb.enqueue(ActorMessage.fire_and_forget("overflow", [])) is false
   - Expected: mb.len() equals `1`
   - Expected: mb.is_full() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("create a one-slot mailbox and fill it")
val mb = ActorMailbox.new(1)
expect(mb.enqueue(ActorMessage.fire_and_forget("only", []))).to_equal(true)
step("attempt to exceed capacity")
# oracle: admission must be bounded — the overflow send is refused, not queued
expect(mb.enqueue(ActorMessage.fire_and_forget("overflow", []))).to_equal(false)
expect(mb.len()).to_equal(1)
expect(mb.is_full()).to_equal(true)
```

</details>

#### marks reply-expecting messages and closes admission on demand

- enqueue a reply-expecting message
   - Expected: mb.enqueue(ActorMessage.with_reply("ask", ["1"], 7)) is true
   - Expected: msg?.expects_reply() is true
- close the mailbox and confirm further sends are refused
   - Expected: mb.is_closed() is true
   - Expected: mb.enqueue(ActorMessage.fire_and_forget("late", [])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("enqueue a reply-expecting message")
val mb = ActorMailbox.default()
expect(mb.enqueue(ActorMessage.with_reply("ask", ["1"], 7))).to_equal(true)
val msg = mb.dequeue()
expect(msg?.expects_reply()).to_equal(true)
step("close the mailbox and confirm further sends are refused")
mb.close()
# oracle: a closed mailbox preserves accepted work but admits nothing new
expect(mb.is_closed()).to_equal(true)
expect(mb.enqueue(ActorMessage.fire_and_forget("late", []))).to_equal(false)
```

</details>

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2eeb60af79d78d34557a48a010633d553b0d6f06f98ec8d0323e2b6fb824c650`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2eeb60af79d78d34557a48a010633d553b0d6f06f98ec8d0323e2b6fb824c650`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2eeb60af79d78d34557a48a010633d553b0d6f06f98ec8d0323e2b6fb824c650`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/feature/usage/actors_spec.spl
mirror: doc/06_spec/feature/usage/actors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/actors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/actors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/actors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/actors_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers messages in FIFO order through the mailbox' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/actors_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects messages beyond the finite mailbox capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/actors_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks reply-expecting messages and closes admission on demand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
