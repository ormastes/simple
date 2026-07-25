# Ds Utils Specification

> 1. expect stack is empty

<!-- sdn-diagram:id=ds_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ds_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ds_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ds_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect stack is empty
2. expect stack size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack: Stack = Stack.create()
expect stack.is_empty()
expect stack.size() == 0
```

</details>

#### pushes items

1. var stack: Stack = Stack create
2. stack push
3. stack push
4. stack push
5. expect stack size
6. expect not stack is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.push(3)
expect stack.size() == 3
expect not stack.is_empty()
```

</details>

#### pops items in LIFO order

1. var stack: Stack = Stack create
2. stack push
3. stack push
4. stack push
5. expect stack size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var stack: Stack = Stack create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: Stack = Stack.create()
val result = stack.pop()
expect result == nil
```

</details>

#### peeks without removing

1. var stack: Stack = Stack create
2. stack push
3. stack push
4. expect stack size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
val result = stack.peek()
expect result == 2
expect stack.size() == 2
```

</details>

#### clears all items

1. var stack: Stack = Stack create
2. stack push
3. stack push
4. stack clear
5. expect stack is empty
6. expect stack size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack: Stack = Stack.create()
stack.push(1)
stack.push(2)
stack.clear()
expect stack.is_empty()
expect stack.size() == 0
```

</details>

#### converts to list

1. var stack: Stack = Stack create
2. stack push
3. stack push
4. stack push
5. expect list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect queue is empty
2. expect queue size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queue: Queue = Queue.create()
expect queue.is_empty()
expect queue.size() == 0
```

</details>

#### enqueues items

1. var queue: Queue = Queue create
2. queue enqueue
3. queue enqueue
4. queue enqueue
5. expect queue size
6. expect not queue is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
queue.enqueue(3)
expect queue.size() == 3
expect not queue.is_empty()
```

</details>

#### dequeues items in FIFO order

1. var queue: Queue = Queue create
2. queue enqueue
3. queue enqueue
4. queue enqueue
5. expect queue size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var queue: Queue = Queue create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue: Queue = Queue.create()
val result = queue.dequeue()
expect result == nil
```

</details>

#### peeks without removing

1. var queue: Queue = Queue create
2. queue enqueue
3. queue enqueue
4. expect queue size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue: Queue = Queue.create()
queue.enqueue(1)
queue.enqueue(2)
val result = queue.peek()
expect result == 1
expect queue.size() == 2
```

</details>

#### clears all items

1. var queue: Queue = Queue create
2. queue enqueue
3. queue enqueue
4. queue clear
5. expect queue is empty
6. expect queue size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect deque is empty
2. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deque: Deque = Deque.create()
expect deque.is_empty()
expect deque.size() == 0
```

</details>

#### pushes to front

1. var deque: Deque = Deque create
2. deque push front
3. deque push front
4. deque push front
5. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var deque: Deque = Deque create
2. deque push back
3. deque push back
4. deque push back
5. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var deque: Deque = Deque create
2. deque push back
3. deque push back
4. deque push back
5. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var deque: Deque = Deque create
2. deque push back
3. deque push back
4. deque push back
5. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var deque: Deque = Deque create


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque: Deque = Deque.create()
val result = deque.pop_front()
expect result == nil
val result = deque.pop_back()
expect result == nil
```

</details>

#### clears all items

1. var deque: Deque = Deque create
2. deque push back
3. deque push back
4. deque clear
5. expect deque is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque: Deque = Deque.create()
deque.push_back(1)
deque.push_back(2)
deque.clear()
expect deque.is_empty()
```

</details>

### Helper Functions

#### creates stack from list

1. var stack = stack from list
2. expect stack size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([1, 2, 3])
expect stack.size() == 3
val result = stack.peek()
expect result == 3
```

</details>

#### creates queue from list

1. expect queue size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queue = queue_from_list([1, 2, 3])
expect queue.size() == 3
val result = queue.peek()
expect result == 1
```

</details>

#### creates deque from list

1. var deque = deque from list
2. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = deque_from_list([1, 2, 3])
expect deque.size() == 3
```

</details>

#### gets element from stack by index

1. var stack = stack from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([1, 2, 3])
val result = stack_get(stack, 0)
expect result == 3
val result = stack_get(stack, 2)
expect result == 1
```

</details>

#### returns nil for out of bounds stack access

1. var stack = stack from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([1, 2, 3])
val result = stack_get(stack, 10)
expect result == nil
```

</details>

#### gets element from queue by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queue = queue_from_list([1, 2, 3])
val result = queue_get(queue, 0)
expect result == 1
val result = queue_get(queue, 2)
expect result == 3
```

</details>

#### returns nil for out of bounds queue access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queue = queue_from_list([1, 2, 3])
val result = queue_get(queue, 10)
expect result == nil
```

</details>

#### reverses stack

1. var stack = stack from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([1, 2, 3])
val reversed = reverse_stack(stack)
val result = reversed.peek()
expect result == 1
```

</details>

#### merges queues

1. expect merged size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q1 = queue_from_list([1, 2])
val q2 = queue_from_list([3, 4])
val merged = merge_queues(q1=q1, q2=q2)
expect merged.size() == 4
```

</details>

### Complex Scenarios

#### handles multiple stack operations

1. var stack: Stack = Stack create
2. stack push
3. stack push
4. stack pop
5. stack push
6. stack push
7. expect stack size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var queue: Queue = Queue create
2. queue enqueue
3. queue enqueue
4. queue dequeue
5. queue enqueue
6. queue enqueue
7. expect queue size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var deque: Deque = Deque create
2. deque push back
3. deque push front
4. deque push back
5. deque pop front
6. expect deque size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/tooling/ds_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
