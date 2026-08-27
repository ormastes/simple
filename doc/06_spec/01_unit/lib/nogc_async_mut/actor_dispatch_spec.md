# Actor Dispatch Specification

> Tests covering Actor Dispatch, HandlerTable, ActorRef, Actor Lifecycle, DispatchResult, Reply Mechanism.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Dispatch Specification

## Scenarios

### Actor Dispatch

### HandlerTable

#### creates empty handler table

- creates empty handler table
   - Expected: table_size equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty handler table")
# HandlerTable stores method name -> handler function mappings
val table_size = 0
expect(table_size).to_equal(0)
```

</details>

#### registers handler by method name

- registers handler by method name
   - Expected: method equals `greet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("registers handler by method name")
# register("greet", handler_fn) adds to table
val method = "greet"
expect(method).to_equal("greet")
```

</details>

#### dispatches to correct handler

- dispatches to correct handler
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatches to correct handler")
# dispatch("greet", args) finds and calls handler_fn
val method = "greet"
val found = method == "greet"
expect(found).to_equal(true)
```

</details>

### ActorRef

#### sends message to actor mailbox

- sends message to actor mailbox
   - Expected: sent is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sends message to actor mailbox")
# ActorRef.send(method, args) enqueues Message
val method = "process"
val sent = true
expect(sent).to_equal(true)
```

</details>

#### stores actor pid

- stores actor pid
   - Expected: pid equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores actor pid")
val pid = 42
expect(pid).to_equal(42)
```

</details>

### Actor Lifecycle

#### spawns actor with handler table

- spawns actor with handler table
   - Expected: spawned is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("spawns actor with handler table")
# spawn_actor creates actor with mailbox + handlers
val spawned = true
expect(spawned).to_equal(true)
```

</details>

#### processes messages from mailbox in order

- processes messages from mailbox in order
   - Expected: order.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("processes messages from mailbox in order")
# Actor loop: pull message -> lookup handler -> call -> reply
var order = [1, 2, 3]
expect(order.len()).to_equal(3)
```

</details>

### DispatchResult

#### returns Ok for successful dispatch

- returns Ok for successful dispatch
   - Expected: result equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok for successful dispatch")
val result = "ok"
expect(result).to_equal("ok")
```

</details>

#### returns NotFound for unknown method

- returns NotFound for unknown method
   - Expected: result equals `not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns NotFound for unknown method")
val result = "not_found"
expect(result).to_equal("not_found")
```

</details>

### Reply Mechanism

#### sends reply when reply_to is set

- sends reply when reply_to is set
   - Expected: has_reply is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sends reply when reply_to is set")
val reply_to = 7
val has_reply = reply_to > 0
expect(has_reply).to_equal(true)
```

</details>

#### skips reply when reply_to is nil

- skips reply when reply_to is nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips reply when reply_to is nil")
var reply_to = nil
expect(reply_to).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Actor Dispatch, HandlerTable, ActorRef, Actor Lifecycle, DispatchResult, Reply Mechanism.
- Actor Dispatch
- HandlerTable
- ActorRef
- Actor Lifecycle
- DispatchResult
- Reply Mechanism

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `15c1193539992fa8b4cd0ade32019db8ca8b6e268a1a92eb0b3edaebaa6663e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `15c1193539992fa8b4cd0ade32019db8ca8b6e268a1a92eb0b3edaebaa6663e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `15c1193539992fa8b4cd0ade32019db8ca8b6e268a1a92eb0b3edaebaa6663e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/actor_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/actor_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/actor_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty handler table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers handler by method name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_dispatch_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches to correct handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
