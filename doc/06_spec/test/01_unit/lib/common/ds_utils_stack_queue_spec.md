# Ds Utils Stack Queue Specification

> 1. var stack = Stack

<!-- sdn-diagram:id=ds_utils_stack_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ds_utils_stack_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ds_utils_stack_queue_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ds_utils_stack_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ds Utils Stack Queue Specification

## Scenarios

### Stack creation

#### creates empty stack via Stack.create

1. var stack = Stack
   - Expected: empty is true
   - Expected: stack.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
val empty = stack.is_empty()
expect(empty).to_equal(true)
expect(stack.size()).to_equal(0)
```

</details>

### Stack push and pop

#### pushes an item onto stack

1. var stack = Stack
2. stack push
   - Expected: stack.size() equals `1`
   - Expected: empty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
stack.push(42)
expect(stack.size()).to_equal(1)
val empty = stack.is_empty()
expect(empty).to_equal(false)
```

</details>

#### pops items in LIFO order

1. var stack = Stack
2. stack push
3. stack push
4. stack push
   - Expected: a equals `3`
   - Expected: b equals `2`
   - Expected: c equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
stack.push(1)
stack.push(2)
stack.push(3)
val a = stack.pop()
val b = stack.pop()
val c = stack.pop()
expect(a).to_equal(3)
expect(b).to_equal(2)
expect(c).to_equal(1)
```

</details>

#### pop returns nil on empty stack

1. var stack = Stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
val result = stack.pop()
expect(result).to_be_nil()
```

</details>

#### push and pop maintain correct size

1. var stack = Stack
2. stack push
3. stack push
   - Expected: stack.size() equals `2`
4. stack pop
   - Expected: stack.size() equals `1`
5. stack pop
   - Expected: stack.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
stack.push(10)
stack.push(20)
expect(stack.size()).to_equal(2)
stack.pop()
expect(stack.size()).to_equal(1)
stack.pop()
expect(stack.size()).to_equal(0)
```

</details>

### Stack peek

#### peeks at top element without removing

1. var stack = Stack
2. stack push
3. stack push
   - Expected: top equals `20`
   - Expected: stack.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
stack.push(10)
stack.push(20)
val top = stack.peek()
expect(top).to_equal(20)
expect(stack.size()).to_equal(2)
```

</details>

#### peek returns nil on empty stack

1. var stack = Stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
val result = stack.peek()
expect(result).to_be_nil()
```

</details>

### Stack clear

#### clears all items

1. var stack = Stack
2. stack push
3. stack push
4. stack push
5. stack clear
   - Expected: empty is true
   - Expected: stack.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
stack.push(1)
stack.push(2)
stack.push(3)
stack.clear()
val empty = stack.is_empty()
expect(empty).to_equal(true)
expect(stack.size()).to_equal(0)
```

</details>

### Stack to_list

#### returns internal item list

1. var stack = Stack
2. stack push
3. stack push
4. stack push
   - Expected: list.len() equals `3`
   - Expected: list[0] equals `1`
   - Expected: list[1] equals `2`
   - Expected: list[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = Stack(items: [])
stack.push(1)
stack.push(2)
stack.push(3)
val list = stack.to_list()
expect(list.len()).to_equal(3)
expect(list[0]).to_equal(1)
expect(list[1]).to_equal(2)
expect(list[2]).to_equal(3)
```

</details>

### Queue creation

#### creates empty queue

1. var queue = Queue
   - Expected: empty is true
   - Expected: queue.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
val empty = queue.is_empty()
expect(empty).to_equal(true)
expect(queue.size()).to_equal(0)
```

</details>

### Queue enqueue and dequeue

#### enqueues items

1. var queue = Queue
2. queue enqueue
3. queue enqueue
   - Expected: queue.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
queue.enqueue(10)
queue.enqueue(20)
expect(queue.size()).to_equal(2)
```

</details>

#### dequeues items in FIFO order

1. var queue = Queue
2. queue enqueue
3. queue enqueue
4. queue enqueue
   - Expected: a equals `1`
   - Expected: b equals `2`
   - Expected: c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
queue.enqueue(1)
queue.enqueue(2)
queue.enqueue(3)
val a = queue.dequeue()
val b = queue.dequeue()
val c = queue.dequeue()
expect(a).to_equal(1)
expect(b).to_equal(2)
expect(c).to_equal(3)
```

</details>

#### dequeue returns nil on empty queue

1. var queue = Queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
val result = queue.dequeue()
expect(result).to_be_nil()
```

</details>

#### enqueue and dequeue maintain correct size

1. var queue = Queue
2. queue enqueue
3. queue enqueue
   - Expected: queue.size() equals `2`
4. queue dequeue
   - Expected: queue.size() equals `1`
5. queue dequeue
   - Expected: queue.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
queue.enqueue(10)
queue.enqueue(20)
expect(queue.size()).to_equal(2)
queue.dequeue()
expect(queue.size()).to_equal(1)
queue.dequeue()
expect(queue.size()).to_equal(0)
```

</details>

### Queue peek

#### peeks at front element without removing

1. var queue = Queue
2. queue enqueue
3. queue enqueue
   - Expected: front equals `10`
   - Expected: queue.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
queue.enqueue(10)
queue.enqueue(20)
val front = queue.peek()
expect(front).to_equal(10)
expect(queue.size()).to_equal(2)
```

</details>

#### peek returns nil on empty queue

1. var queue = Queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
val result = queue.peek()
expect(result).to_be_nil()
```

</details>

### Queue clear

#### clears all items

1. var queue = Queue
2. queue enqueue
3. queue enqueue
4. queue clear
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = Queue(items: [])
queue.enqueue(1)
queue.enqueue(2)
queue.clear()
val empty = queue.is_empty()
expect(empty).to_equal(true)
```

</details>

### Deque creation

#### creates empty deque

1. var deque = Deque
   - Expected: empty is true
   - Expected: deque.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
val empty = deque.is_empty()
expect(empty).to_equal(true)
expect(deque.size()).to_equal(0)
```

</details>

### Deque push operations

#### push_back adds to end

1. var deque = Deque
2. deque push back
3. deque push back
   - Expected: front equals `1`
   - Expected: back equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_back(1)
deque.push_back(2)
val front = deque.peek_front()
val back = deque.peek_back()
expect(front).to_equal(1)
expect(back).to_equal(2)
```

</details>

#### push_front adds to beginning

1. var deque = Deque
2. deque push front
3. deque push front
   - Expected: front equals `2`
   - Expected: back equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_front(1)
deque.push_front(2)
val front = deque.peek_front()
val back = deque.peek_back()
expect(front).to_equal(2)
expect(back).to_equal(1)
```

</details>

#### push_front and push_back together

1. var deque = Deque
2. deque push back
3. deque push front
4. deque push back
   - Expected: front equals `1`
   - Expected: back equals `3`
   - Expected: deque.size() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_back(2)
deque.push_front(1)
deque.push_back(3)
val front = deque.peek_front()
val back = deque.peek_back()
expect(front).to_equal(1)
expect(back).to_equal(3)
expect(deque.size()).to_equal(3)
```

</details>

### Deque pop operations

#### pop_front removes from beginning

1. var deque = Deque
2. deque push back
3. deque push back
4. deque push back
   - Expected: a equals `1`
   - Expected: deque.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_back(1)
deque.push_back(2)
deque.push_back(3)
val a = deque.pop_front()
expect(a).to_equal(1)
expect(deque.size()).to_equal(2)
```

</details>

#### pop_back removes from end

1. var deque = Deque
2. deque push back
3. deque push back
4. deque push back
   - Expected: a equals `3`
   - Expected: deque.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_back(1)
deque.push_back(2)
deque.push_back(3)
val a = deque.pop_back()
expect(a).to_equal(3)
expect(deque.size()).to_equal(2)
```

</details>

#### pop_front returns nil on empty deque

1. var deque = Deque


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
val result = deque.pop_front()
expect(result).to_be_nil()
```

</details>

#### pop_back returns nil on empty deque

1. var deque = Deque


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
val result = deque.pop_back()
expect(result).to_be_nil()
```

</details>

### Deque peek operations

#### peek_front returns nil on empty deque

1. var deque = Deque


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
val result = deque.peek_front()
expect(result).to_be_nil()
```

</details>

#### peek_back returns nil on empty deque

1. var deque = Deque


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
val result = deque.peek_back()
expect(result).to_be_nil()
```

</details>

#### peek does not modify deque

1. var deque = Deque
2. deque push back
3. deque push back
4. deque peek front
5. deque peek back
   - Expected: deque.size() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_back(10)
deque.push_back(20)
deque.peek_front()
deque.peek_back()
expect(deque.size()).to_equal(2)
```

</details>

### Deque clear

#### clears all items

1. var deque = Deque
2. deque push back
3. deque push front
4. deque clear
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = Deque(items: [])
deque.push_back(1)
deque.push_front(0)
deque.clear()
val empty = deque.is_empty()
expect(empty).to_equal(true)
```

</details>

### stack_from_list

#### creates stack from list of items

1. var stack = stack from list
   - Expected: stack.size() equals `3`
   - Expected: top equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([10, 20, 30])
expect(stack.size()).to_equal(3)
val top = stack.peek()
expect(top).to_equal(30)
```

</details>

#### creates empty stack from empty list

1. var stack = stack from list
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([])
val empty = stack.is_empty()
expect(empty).to_equal(true)
```

</details>

### queue_from_list

#### creates queue from list of items

1. var queue = queue from list
   - Expected: queue.size() equals `3`
   - Expected: front equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = queue_from_list([10, 20, 30])
expect(queue.size()).to_equal(3)
val front = queue.peek()
expect(front).to_equal(10)
```

</details>

#### creates empty queue from empty list

1. var queue = queue from list
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = queue_from_list([])
val empty = queue.is_empty()
expect(empty).to_equal(true)
```

</details>

### deque_from_list

#### creates deque from list of items

1. var deque = deque from list
   - Expected: deque.size() equals `3`
   - Expected: front equals `10`
   - Expected: back equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = deque_from_list([10, 20, 30])
expect(deque.size()).to_equal(3)
val front = deque.peek_front()
val back = deque.peek_back()
expect(front).to_equal(10)
expect(back).to_equal(30)
```

</details>

#### creates empty deque from empty list

1. var deque = deque from list
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deque = deque_from_list([])
val empty = deque.is_empty()
expect(empty).to_equal(true)
```

</details>

### stack_get

#### gets element by index from top (0 = top)

1. var stack = stack from list
   - Expected: top equals `30`
   - Expected: mid equals `20`
   - Expected: bot equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([10, 20, 30])
val top = stack_get(stack, 0)
expect(top).to_equal(30)
val mid = stack_get(stack, 1)
expect(mid).to_equal(20)
val bot = stack_get(stack, 2)
expect(bot).to_equal(10)
```

</details>

#### returns nil for out-of-bounds index

1. var stack = stack from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([10, 20])
val result = stack_get(stack, 5)
expect(result).to_be_nil()
```

</details>

### queue_get

#### gets element by index from front (0 = front)

1. var queue = queue from list
   - Expected: front equals `10`
   - Expected: mid equals `20`
   - Expected: back equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = queue_from_list([10, 20, 30])
val front = queue_get(queue, 0)
expect(front).to_equal(10)
val mid = queue_get(queue, 1)
expect(mid).to_equal(20)
val back = queue_get(queue, 2)
expect(back).to_equal(30)
```

</details>

#### returns nil for out-of-bounds index

1. var queue = queue from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = queue_from_list([10, 20])
val result = queue_get(queue, 5)
expect(result).to_be_nil()
```

</details>

### reverse_stack

#### reverses a stack

1. var stack = stack from list
2. var reversed = reverse stack
   - Expected: top equals `1`
   - Expected: a equals `1`
   - Expected: b equals `2`
   - Expected: c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([1, 2, 3])
var reversed = reverse_stack(stack)
val top = reversed.peek()
expect(top).to_equal(1)
val a = reversed.pop()
expect(a).to_equal(1)
val b = reversed.pop()
expect(b).to_equal(2)
val c = reversed.pop()
expect(c).to_equal(3)
```

</details>

#### reversing empty stack returns empty

1. var stack = stack from list
2. var reversed = reverse stack
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([])
var reversed = reverse_stack(stack)
val empty = reversed.is_empty()
expect(empty).to_equal(true)
```

</details>

#### reversing single element returns same

1. var stack = stack from list
2. var reversed = reverse stack
   - Expected: top equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stack = stack_from_list([42])
var reversed = reverse_stack(stack)
val top = reversed.peek()
expect(top).to_equal(42)
```

</details>

### merge_queues

#### merges two queues

1. var q1 = queue from list
2. var q2 = queue from list
3. var merged = merge queues
   - Expected: merged.size() equals `4`
   - Expected: a equals `1`
   - Expected: b equals `2`
   - Expected: c equals `3`
   - Expected: d equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q1 = queue_from_list([1, 2])
var q2 = queue_from_list([3, 4])
var merged = merge_queues(q1, q2)
expect(merged.size()).to_equal(4)
val a = merged.dequeue()
val b = merged.dequeue()
val c = merged.dequeue()
val d = merged.dequeue()
expect(a).to_equal(1)
expect(b).to_equal(2)
expect(c).to_equal(3)
expect(d).to_equal(4)
```

</details>

#### merging with empty queue returns copy

1. var q1 = queue from list
2. var q2 = queue from list
3. var merged = merge queues
   - Expected: merged.size() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q1 = queue_from_list([1, 2, 3])
var q2 = queue_from_list([])
var merged = merge_queues(q1, q2)
expect(merged.size()).to_equal(3)
```

</details>

#### merging two empty queues returns empty

1. var q1 = queue from list
2. var q2 = queue from list
3. var merged = merge queues
   - Expected: empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q1 = queue_from_list([])
var q2 = queue_from_list([])
var merged = merge_queues(q1, q2)
val empty = merged.is_empty()
expect(empty).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ds_utils_stack_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stack creation
- Stack push and pop
- Stack peek
- Stack clear
- Stack to_list
- Queue creation
- Queue enqueue and dequeue
- Queue peek
- Queue clear
- Deque creation
- Deque push operations
- Deque pop operations
- Deque peek operations
- Deque clear
- stack_from_list
- queue_from_list
- deque_from_list
- stack_get
- queue_get
- reverse_stack
- merge_queues

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
