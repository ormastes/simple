# concurrency_primitives_spec

> use std.nogc_async_mut.{mpsc_queue_new, atomic_flag_new, once_new, barrier_new}

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# concurrency_primitives_spec

use std.nogc_async_mut.{mpsc_queue_new, atomic_flag_new, once_new, barrier_new}

## At a Glance

| Field | Value |
|-------|-------|
| Category | Concurrency |
| Status | Active |
| Source | `test/03_system/feature/usage/concurrency_primitives_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
use std.nogc_async_mut.{mpsc_queue_new, atomic_flag_new, once_new, barrier_new}

var queue = mpsc_queue_new()
queue.push(42)
val item = queue.pop()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| MpscQueue | Multi-producer, single-consumer message queue |
| AtomicFlag | Test-and-set flag for lock-free signaling |
| Once | One-time initialization latch |
| Barrier | Rendezvous point for a fixed number of participants |

## Scenarios

### Concurrency Primitives

#### delivers queued messages in FIFO order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- delivers queued messages in FIFO order
- Push three messages and drain the queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delivers queued messages in FIFO order")
step("Push three messages and drain the queue")
var queue = mpsc_queue_new()
queue.push(1)
queue.push(2)
queue.push(3)

expect queue.len() == 3
expect queue.pop() == 1
expect queue.pop() == 2
expect queue.pop() == 3
expect queue.is_empty() == true
```

</details>

#### signals through an atomic flag with test-and-set

- signals through an atomic flag with test-and-set
- First test-and-set flips the flag, second observes it set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("signals through an atomic flag with test-and-set")
step("First test-and-set flips the flag, second observes it set")
var flag = atomic_flag_new()
expect flag.test_and_set() == false
expect flag.test_and_set() == true
flag.clear()
expect flag.test_and_set() == false
```

</details>

#### runs one-time initialization exactly once

- runs one-time initialization exactly once
- Call once twice; the latch completes and stays completed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs one-time initialization exactly once")
step("Call once twice; the latch completes and stays completed")
var latch = once_new()
expect latch.is_completed() == false
latch.call_once(fn(): pass_dn)
latch.call_once(fn(): pass_dn)
expect latch.is_completed() == true
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

- Canonical SPipe generation for source `919cbf97dd7372ac0cd37f6b39f48f6bb6d87916e66e05da79747a508964692f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `919cbf97dd7372ac0cd37f6b39f48f6bb6d87916e66e05da79747a508964692f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `919cbf97dd7372ac0cd37f6b39f48f6bb6d87916e66e05da79747a508964692f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/concurrency_primitives_spec.spl
mirror: doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/concurrency_primitives_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers queued messages in FIFO order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/concurrency_primitives_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signals through an atomic flag with test-and-set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/concurrency_primitives_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs one-time initialization exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
