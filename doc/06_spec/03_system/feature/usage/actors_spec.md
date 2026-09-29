# Actor Model Concurrency

> The actor model provides a message-passing concurrency primitive where isolated actors communicate exclusively through asynchronous messages. Each actor encapsulates its own state and processes messages sequentially from a mailbox, eliminating shared-state races. As a user of the actor API I spawn actors, register message handlers, and exchange messages through mailboxes, so that concurrent workers stay isolated behind a message-passing boundary instead of shared mutable state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Model Concurrency

The actor model provides a message-passing concurrency primitive where isolated actors communicate exclusively through asynchronous messages. Each actor encapsulates its own state and processes messages sequentially from a mailbox, eliminating shared-state races. As a user of the actor API I spawn actors, register message handlers, and exchange messages through mailboxes, so that concurrent workers stay isolated behind a message-passing boundary instead of shared mutable state.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RUNTIME-010 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/actors_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The actor model provides a message-passing concurrency primitive where isolated actors
communicate exclusively through asynchronous messages. Each actor encapsulates its own
state and processes messages sequentially from a mailbox, eliminating shared-state races.
As a user of the actor API I spawn actors, register message handlers, and exchange
messages through mailboxes, so that concurrent workers stay isolated behind a
message-passing boundary instead of shared mutable state.

## Syntax

```simple
use std.nogc_async_mut.actors.actor.{make_handlers, spawn_actor}

var handlers = make_handlers()
handlers.register("double", double_handler)
val worker = spawn_actor(handlers)
worker.send("double", ["21"])
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

#### dispatches a message to the registered handler and returns its result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- register handler and dispatch a message through the handler table
   - Expected: result.is_ok() is true
   - Expected: result.value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("register handler and dispatch a message through the handler table")
var handlers = make_handlers()
handlers.register("double", double_handler)

val result = handlers.dispatch("double", ["21"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("42")
```

</details>

#### spawning two actors yields distinct actor identities

- spawn two actors from the same handler table


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spawn two actors from the same handler table")
var handlers = make_handlers()
handlers.register("double", double_handler)

val worker_a = spawn_actor(handlers)
val worker_b = spawn_actor(handlers)

expect(worker_a.get_id()).to_not_equal(worker_b.get_id())
```

</details>

#### dispatching an unregistered method fails closed with a named error

- dispatch a method the actor never registered
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatch a method the actor never registered")
var handlers = make_handlers()
handlers.register("double", double_handler)

val result = handlers.dispatch("no_such_method", ["1"])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("no_such_method")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1306d5a75b0757e873977bee6216815f609c3eda23567a788267e628576abc33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1306d5a75b0757e873977bee6216815f609c3eda23567a788267e628576abc33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1306d5a75b0757e873977bee6216815f609c3eda23567a788267e628576abc33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/actors_spec.spl
mirror: doc/06_spec/03_system/feature/usage/actors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/actors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/actors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/actors_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches a message to the registered handler and returns its result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/actors_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawning two actors yields distinct actor identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/actors_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatching an unregistered method fails closed with a named error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
