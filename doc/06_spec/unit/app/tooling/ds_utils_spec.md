# Ds Utils Specification

> Tests covering Data Structure Utilities, Stack, Queue, Deque, Helper Functions, Complex Scenarios.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ds Utils Specification

## Scenarios

### Data Structure Utilities

### Stack

#### creates empty stack

- creates empty stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty stack")
val stack: Stack = Stack.create()
expect stack.is_empty()
expect stack.size() == 0
```

</details>

#### pushes items

- pushes items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes items")
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.push(3)
expect stack.size() == 3
expect not stack.is_empty()
```

</details>

#### pops items in LIFO order

- pops items in LIFO order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pops items in LIFO order")
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.push(3)
val result1 = stack.pop()
expect result1 == 3
val result2 = stack.pop()
expect result2 == 2
expect stack.size() == 1
```

</details>

#### returns nil when popping empty stack

- returns nil when popping empty stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when popping empty stack")
var stack: Stack = Stack.create()
val result = stack.pop()
expect result == nil
```

</details>

#### peeks without removing

- peeks without removing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("peeks without removing")
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
val result = stack.peek()
expect result == 2
expect stack.size() == 2
```

</details>

#### clears all items

- clears all items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all items")
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.clear()
expect stack.is_empty()
expect stack.size() == 0
```

</details>

#### converts to list

- converts to list


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to list")
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.push(3)
val list = stack.to_list()
expect list.len() == 3
expect list[0] == 1
expect list[2] == 3
```

</details>

### Queue

#### creates empty queue

- creates empty queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty queue")
val queue: Queue = Queue.create()
expect queue.is_empty()
expect queue.size() == 0
```

</details>

#### enqueues items

- enqueues items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enqueues items")
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
queue.enqueue(3)
expect queue.size() == 3
expect not queue.is_empty()
```

</details>

#### dequeues items in FIFO order

- dequeues items in FIFO order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dequeues items in FIFO order")
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
queue.enqueue(3)
val result1 = queue.dequeue()
expect result1 == 1
val result2 = queue.dequeue()
expect result2 == 2
expect queue.size() == 1
```

</details>

#### returns nil when dequeuing empty queue

- returns nil when dequeuing empty queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when dequeuing empty queue")
var queue: Queue = Queue.create()
val result = queue.dequeue()
expect result == nil
```

</details>

#### peeks without removing

- peeks without removing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("peeks without removing")
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
val result = queue.peek()
expect result == 1
expect queue.size() == 2
```

</details>

#### clears all items

- clears all items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all items")
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
queue.clear()
expect queue.is_empty()
expect queue.size() == 0
```

</details>

### Deque

#### creates empty deque

- creates empty deque


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty deque")
val deque: Deque = Deque.create()
expect deque.is_empty()
expect deque.size() == 0
```

</details>

#### pushes to front

- pushes to front


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes to front")
var deque: Deque = Deque.create()
deque.push_front(1)
deque.push_front(2)
deque.push_front(3)
expect deque.size() == 3
val result = deque.peek_front()
expect result == 3
```

</details>

#### pushes to back

- pushes to back


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes to back")
var deque: Deque = Deque.create()
deque.push_back(1)
deque.push_back(2)
deque.push_back(3)
expect deque.size() == 3
val result = deque.peek_back()
expect result == 3
```

</details>

#### pops from front

- pops from front


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pops from front")
var deque: Deque = Deque.create()
deque.push_back(1)
deque.push_back(2)
deque.push_back(3)
val result = deque.pop_front()
expect result == 1
expect deque.size() == 2
```

</details>

#### pops from back

- pops from back


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pops from back")
var deque: Deque = Deque.create()
deque.push_back(1)
deque.push_back(2)
deque.push_back(3)
val result = deque.pop_back()
expect result == 3
expect deque.size() == 2
```

</details>

#### returns nil when popping empty deque

- returns nil when popping empty deque


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when popping empty deque")
var deque: Deque = Deque.create()
val result = deque.pop_front()
expect result == nil
val result = deque.pop_back()
expect result == nil
```

</details>

#### clears all items

- clears all items


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all items")
var deque: Deque = Deque.create()
deque.push_back(1)
deque.push_back(2)
deque.clear()
expect deque.is_empty()
```

</details>

### Helper Functions

#### creates stack from list

- creates stack from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stack from list")
var stack = stack_from_list([1, 2, 3])
expect stack.size() == 3
val result = stack.peek()
expect result == 3
```

</details>

#### creates queue from list

- creates queue from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates queue from list")
val queue = queue_from_list([1, 2, 3])
expect queue.size() == 3
val result = queue.peek()
expect result == 1
```

</details>

#### creates deque from list

- creates deque from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates deque from list")
var deque = deque_from_list([1, 2, 3])
expect deque.size() == 3
```

</details>

#### gets element from stack by index

- gets element from stack by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets element from stack by index")
var stack = stack_from_list([1, 2, 3])
val result = stack_get(stack, 0)
expect result == 3
val result = stack_get(stack, 2)
expect result == 1
```

</details>

#### returns nil for out of bounds stack access

- returns nil for out of bounds stack access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for out of bounds stack access")
var stack = stack_from_list([1, 2, 3])
val result = stack_get(stack, 10)
expect result == nil
```

</details>

#### gets element from queue by index

- gets element from queue by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets element from queue by index")
val queue = queue_from_list([1, 2, 3])
val result = queue_get(queue, 0)
expect result == 1
val result = queue_get(queue, 2)
expect result == 3
```

</details>

#### returns nil for out of bounds queue access

- returns nil for out of bounds queue access


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for out of bounds queue access")
val queue = queue_from_list([1, 2, 3])
val result = queue_get(queue, 10)
expect result == nil
```

</details>

#### reverses stack

- reverses stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses stack")
var stack = stack_from_list([1, 2, 3])
val reversed = reverse_stack(stack)
val result = reversed.peek()
expect result == 1
```

</details>

#### merges queues

- merges queues


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges queues")
val q1 = queue_from_list([1, 2])
val q2 = queue_from_list([3, 4])
val merged = merge_queues(q1=q1, q2=q2)
expect merged.size() == 4
```

</details>

### Complex Scenarios

#### handles multiple stack operations

- handles multiple stack operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple stack operations")
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.pop()
stack.push(3)
stack.push(4)
expect stack.size() == 3
val result = stack.pop()
expect result == 4
```

</details>

#### handles multiple queue operations

- handles multiple queue operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple queue operations")
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
queue.dequeue()
queue.enqueue(3)
queue.enqueue(4)
expect queue.size() == 3
val result = queue.dequeue()
expect result == 2
```

</details>

#### handles mixed deque operations

- handles mixed deque operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mixed deque operations")
var deque: Deque = Deque.create()
deque.push_back(1)
deque.push_front(2)
deque.push_back(3)
deque.pop_front()
expect deque.size() == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/ds_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Data Structure Utilities, Stack, Queue, Deque, Helper Functions, Complex Scenarios.
- Data Structure Utilities
- Stack
- Queue
- Deque
- Helper Functions
- Complex Scenarios

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `7e2c083fc1a8212e4a7c1fa36995fb8f70c73cc59cc47824b87bf1b16cdade70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e2c083fc1a8212e4a7c1fa36995fb8f70c73cc59cc47824b87bf1b16cdade70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e2c083fc1a8212e4a7c1fa36995fb8f70c73cc59cc47824b87bf1b16cdade70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/ds_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/ds_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/ds_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/ds_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/ds_utils_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty stack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/ds_utils_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/ds_utils_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pops items in LIFO order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
