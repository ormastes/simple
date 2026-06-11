# Channel Intensive Tests

> Intensive tests for channel-based message passing: unbounded and bounded channels, send/recv/try_recv, close semantics, and multi-producer patterns.

<!-- sdn-diagram:id=channel_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=channel_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

channel_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=channel_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Channel Intensive Tests

Intensive tests for channel-based message passing: unbounded and bounded channels, send/recv/try_recv, close semantics, and multi-producer patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Source | `test/01_unit/lib/nogc_async_mut/channel_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for channel-based message passing: unbounded and bounded channels,
send/recv/try_recv, close semantics, and multi-producer patterns.

## Scenarios

### Unbounded Channel Basics

#### creates an empty unbounded channel

1. var ch = Channel unbounded
   - Expected: ch.is_empty() is true
   - Expected: ch.len() equals `0`
   - Expected: ch.is_closed() is false
   - Expected: ch.capacity equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
expect(ch.is_empty()).to_equal(true)
expect(ch.len()).to_equal(0)
expect(ch.is_closed()).to_equal(false)
expect(ch.capacity).to_equal(0)
```

</details>

#### sends and receives a single message

1. var ch = Channel unbounded
   - Expected: sent is true
   - Expected: ch.len() equals `1`
   - Expected: received equals `42`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
val sent = ch.send(42)
expect(sent).to_equal(true)
expect(ch.len()).to_equal(1)
val received = ch.try_recv()
expect(received).to_equal(42)
expect(ch.is_empty()).to_equal(true)
```

</details>

#### maintains FIFO order for multiple messages

1. var ch = Channel unbounded
2. ch send
3. ch send
4. ch send
   - Expected: ch.try_recv() equals `1`
   - Expected: ch.try_recv() equals `2`
   - Expected: ch.try_recv() equals `3`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(1)
ch.send(2)
ch.send(3)
expect(ch.try_recv()).to_equal(1)
expect(ch.try_recv()).to_equal(2)
expect(ch.try_recv()).to_equal(3)
expect(ch.is_empty()).to_equal(true)
```

</details>

#### handles interleaved send and recv

1. var ch = Channel unbounded
2. ch send
3. ch send
   - Expected: ch.try_recv() equals `10`
4. ch send
   - Expected: ch.try_recv() equals `20`
   - Expected: ch.try_recv() equals `30`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(10)
ch.send(20)
expect(ch.try_recv()).to_equal(10)
ch.send(30)
expect(ch.try_recv()).to_equal(20)
expect(ch.try_recv()).to_equal(30)
expect(ch.is_empty()).to_equal(true)
```

</details>

### Bounded Channel Basics

#### creates a bounded channel with given capacity

1. var ch = Channel bounded
   - Expected: ch.capacity equals `3`
   - Expected: ch.is_empty() is true
   - Expected: ch.is_full() is false
   - Expected: sent is true
   - Expected: ch.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.bounded(3)
expect(ch.capacity).to_equal(3)
expect(ch.is_empty()).to_equal(true)
expect(ch.is_full()).to_equal(false)
val sent = ch.send(1)
expect(sent).to_equal(true)
expect(ch.len()).to_equal(1)
```

</details>

#### rejects send when bounded channel is full

1. var ch = Channel bounded
   - Expected: ch.send(1) is true
   - Expected: ch.send(2) is true
   - Expected: ch.is_full() is true
   - Expected: ch.send(3) is false
   - Expected: ch.len() equals `2`
   - Expected: v equals `1`
   - Expected: ch.is_full() is false
   - Expected: ch.send(3) is true
   - Expected: ch.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.bounded(2)
expect(ch.send(1)).to_equal(true)
expect(ch.send(2)).to_equal(true)
expect(ch.is_full()).to_equal(true)
# Third send should fail
expect(ch.send(3)).to_equal(false)
expect(ch.len()).to_equal(2)
# Recv frees space, then send succeeds
val v = ch.try_recv()
expect(v).to_equal(1)
expect(ch.is_full()).to_equal(false)
expect(ch.send(3)).to_equal(true)
expect(ch.len()).to_equal(2)
```

</details>

#### handles capacity-1 single slot channel

1. var ch = Channel bounded
   - Expected: ch.send(100) is true
   - Expected: ch.is_full() is true
   - Expected: ch.send(200) is false
   - Expected: ch.try_recv() equals `100`
   - Expected: ch.is_empty() is true
   - Expected: ch.send(200) is true
   - Expected: ch.try_recv() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.bounded(1)
expect(ch.send(100)).to_equal(true)
expect(ch.is_full()).to_equal(true)
expect(ch.send(200)).to_equal(false)
expect(ch.try_recv()).to_equal(100)
expect(ch.is_empty()).to_equal(true)
expect(ch.send(200)).to_equal(true)
expect(ch.try_recv()).to_equal(200)
```

</details>

### Channel Close Semantics

#### prevents new sends after close but drains existing messages

1. var ch = Channel unbounded
2. ch send
3. ch send
4. ch close
   - Expected: ch.is_closed() is true
   - Expected: ch.send(3) is false
   - Expected: ch.try_recv() equals `1`
   - Expected: ch.try_recv() equals `2`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(1)
ch.send(2)
ch.close()
expect(ch.is_closed()).to_equal(true)
# Send after close should fail
expect(ch.send(3)).to_equal(false)
# Existing messages still receivable
expect(ch.try_recv()).to_equal(1)
expect(ch.try_recv()).to_equal(2)
expect(ch.is_empty()).to_equal(true)
```

</details>

#### returns sentinel on recv from closed empty channel

1. var ch = Channel unbounded
2. ch close
   - Expected: ch.try_recv() equals `-1`
   - Expected: ch.is_closed() is true
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.close()
expect(ch.try_recv()).to_equal(-1)
expect(ch.is_closed()).to_equal(true)
expect(ch.is_empty()).to_equal(true)
```

</details>

### Channel try_recv

#### returns sentinel when channel is empty

1. var ch = Channel unbounded
   - Expected: ch.try_recv() equals `-1`
   - Expected: ch.is_empty() is true
   - Expected: ch.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
expect(ch.try_recv()).to_equal(-1)
# Still empty after failed recv
expect(ch.is_empty()).to_equal(true)
expect(ch.len()).to_equal(0)
```

</details>

### Channel Drain

#### sends many messages and recvs all in correct FIFO order

1. var ch = Channel unbounded
2. ch send
3. ch send
4. ch send
5. ch send
6. ch send
   - Expected: ch.len() equals `5`
   - Expected: ch.try_recv() equals `0`
   - Expected: ch.try_recv() equals `10`
   - Expected: ch.try_recv() equals `20`
   - Expected: ch.try_recv() equals `30`
   - Expected: ch.try_recv() equals `40`
   - Expected: ch.is_empty() is true
   - Expected: ch.try_recv() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(0)
ch.send(10)
ch.send(20)
ch.send(30)
ch.send(40)
expect(ch.len()).to_equal(5)
# Drain and verify order
expect(ch.try_recv()).to_equal(0)
expect(ch.try_recv()).to_equal(10)
expect(ch.try_recv()).to_equal(20)
expect(ch.try_recv()).to_equal(30)
expect(ch.try_recv()).to_equal(40)
expect(ch.is_empty()).to_equal(true)
expect(ch.try_recv()).to_equal(-1)
```

</details>

### Channel State Checks

#### reports correct state through lifecycle

1. var ch = Channel bounded
   - Expected: ch.is_empty() is true
   - Expected: ch.is_full() is false
   - Expected: ch.is_closed() is false
   - Expected: ch.len() equals `0`
2. ch send
   - Expected: ch.is_empty() is false
   - Expected: ch.is_full() is false
   - Expected: ch.len() equals `1`
3. ch send
4. ch send
   - Expected: ch.is_full() is true
   - Expected: ch.len() equals `3`
5. ch try recv
   - Expected: ch.is_full() is false
   - Expected: ch.len() equals `2`
6. ch close
   - Expected: ch.is_closed() is true
   - Expected: ch.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.bounded(3)
# Initially empty, not full, not closed
expect(ch.is_empty()).to_equal(true)
expect(ch.is_full()).to_equal(false)
expect(ch.is_closed()).to_equal(false)
expect(ch.len()).to_equal(0)
# Fill partially
ch.send(1)
expect(ch.is_empty()).to_equal(false)
expect(ch.is_full()).to_equal(false)
expect(ch.len()).to_equal(1)
# Fill completely
ch.send(2)
ch.send(3)
expect(ch.is_full()).to_equal(true)
expect(ch.len()).to_equal(3)
# Drain one
ch.try_recv()
expect(ch.is_full()).to_equal(false)
expect(ch.len()).to_equal(2)
# Close
ch.close()
expect(ch.is_closed()).to_equal(true)
# Remaining messages still accessible
expect(ch.len()).to_equal(2)
```

</details>

### Channel Edge Cases

#### sends and receives zero

1. var ch = Channel unbounded
2. ch send
   - Expected: ch.len() equals `1`
   - Expected: ch.try_recv() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(0)
expect(ch.len()).to_equal(1)
expect(ch.try_recv()).to_equal(0)
```

</details>

#### sends and receives negative values

1. var ch = Channel unbounded
2. ch send
3. ch send
   - Expected: ch.try_recv() equals `-42`
   - Expected: ch.try_recv() equals `-100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(-42)
ch.send(-100)
expect(ch.try_recv()).to_equal(-42)
expect(ch.try_recv()).to_equal(-100)
```

</details>

#### recv from closed channel with data returns data then sentinel

1. var ch = Channel unbounded
2. ch send
3. ch send
4. ch close
   - Expected: ch.try_recv() equals `5`
   - Expected: ch.try_recv() equals `10`
   - Expected: ch.try_recv() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(5)
ch.send(10)
ch.close()
expect(ch.try_recv()).to_equal(5)
expect(ch.try_recv()).to_equal(10)
expect(ch.try_recv()).to_equal(-1)
```

</details>

### Multi-Producer Pattern

#### simulates multiple producers filling a shared channel

1. var ch = Channel unbounded
2. ch send
3. ch send
4. ch send
5. ch send
6. ch send
7. ch send
   - Expected: ch.len() equals `6`
   - Expected: ch.try_recv() equals `1`
   - Expected: ch.try_recv() equals `2`
   - Expected: ch.try_recv() equals `3`
   - Expected: ch.try_recv() equals `100`
   - Expected: ch.try_recv() equals `101`
   - Expected: ch.try_recv() equals `102`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
# Producer A sends values 1..3
ch.send(1)
ch.send(2)
ch.send(3)
# Producer B sends values 100..102
ch.send(100)
ch.send(101)
ch.send(102)
expect(ch.len()).to_equal(6)
# Verify A's messages come first (FIFO within each producer batch)
expect(ch.try_recv()).to_equal(1)
expect(ch.try_recv()).to_equal(2)
expect(ch.try_recv()).to_equal(3)
# Then B's messages
expect(ch.try_recv()).to_equal(100)
expect(ch.try_recv()).to_equal(101)
expect(ch.try_recv()).to_equal(102)
expect(ch.is_empty()).to_equal(true)
```

</details>

### Large Buffer

#### sends 5 items and recvs all in order

1. var ch = Channel unbounded
2. ch send
3. ch send
4. ch send
5. ch send
6. ch send
   - Expected: ch.len() equals `5`
   - Expected: ch.is_full() is false
   - Expected: ch.try_recv() equals `0`
   - Expected: ch.try_recv() equals `1`
   - Expected: ch.try_recv() equals `2`
   - Expected: ch.try_recv() equals `3`
   - Expected: ch.try_recv() equals `4`
   - Expected: ch.is_empty() is true
   - Expected: ch.try_recv() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel.unbounded()
ch.send(0)
ch.send(1)
ch.send(2)
ch.send(3)
ch.send(4)
expect(ch.len()).to_equal(5)
expect(ch.is_full()).to_equal(false)  # unbounded never full
expect(ch.try_recv()).to_equal(0)
expect(ch.try_recv()).to_equal(1)
expect(ch.try_recv()).to_equal(2)
expect(ch.try_recv()).to_equal(3)
expect(ch.try_recv()).to_equal(4)
expect(ch.is_empty()).to_equal(true)
expect(ch.try_recv()).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)


</details>
