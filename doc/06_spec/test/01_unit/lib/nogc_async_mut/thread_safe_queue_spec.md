# Thread Safe Queue Specification

> <details>

<!-- sdn-diagram:id=thread_safe_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_safe_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_safe_queue_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_safe_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Safe Queue Specification

## Scenarios

### Thread Safe Queue

#### should expose mutex protected queue operations

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = queue_source()
expect(src.contains("class ThreadSafeQueue")).to_equal(true)
expect(src.contains("items: [usize]")).to_equal(true)
expect(src.contains("mutex: MutexHandle")).to_equal(true)
expect(src.contains("not_empty: CondVarHandle")).to_equal(true)
```

</details>

#### should create mutex and condition variable resources

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = queue_source()
expect(src.contains("mutex: mutex_create()")).to_equal(true)
expect(src.contains("not_empty: condvar_create()")).to_equal(true)
expect(src.contains("static fn new() -> ThreadSafeQueue")).to_equal(true)
```

</details>

#### should guard push and signal waiters

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = queue_source()
expect(src.contains("me push(item: usize)")).to_equal(true)
expect(src.contains("self.mutex.lock()")).to_equal(true)
expect(src.contains("self.items = self.items.push(item)")).to_equal(true)
expect(src.contains("self.not_empty.signal()")).to_equal(true)
expect(src.contains("self.mutex.unlock()")).to_equal(true)
```

</details>

#### should return zero sentinel for empty or timed out pops

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = queue_source()
expect(src.contains("me try_pop() -> usize")).to_equal(true)
expect(src.contains("me pop_blocking(timeout_ms: i64) -> usize")).to_equal(true)
expect(src.contains("return 0")).to_equal(true)
expect(src.contains("var result = 0")).to_equal(true)
```

</details>

#### should expose size clear and destroy lifecycle methods

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = queue_source()
expect(src.contains("fn len() -> usize")).to_equal(true)
expect(src.contains("fn is_empty() -> bool")).to_equal(true)
expect(src.contains("me clear()")).to_equal(true)
expect(src.contains("me destroy()")).to_equal(true)
expect(src.contains("self.not_empty.destroy()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Thread Safe Queue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
