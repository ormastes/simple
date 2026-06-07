# Actor Heap Specification

> 1. check

<!-- sdn-diagram:id=actor_heap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_heap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_heap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=actor_heap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Heap Specification

## Scenarios

### ActorHeap - Configuration

#### creates with default config

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = ActorHeap.new(HeapConfig.default())
val config = heap.config

check(config.initial_size.value == 2048)
check(config.gc_enabled)
check(config.generational)
```

</details>

#### creates with custom config

1. initial size: ByteSize
2. max size: ByteSize
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HeapConfig(
    initial_size: ByteSize(value: 1024),
    max_size: ByteSize(value: 4096),
    gc_enabled: true,
    generational: false,
    pretenure_threshold: 5
)
val heap = ActorHeap.new(config)

check(heap.config.initial_size.value == 1024)
check(heap.config.max_size.value == 4096)
check(not heap.config.generational)
```

</details>

#### creates small heap

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = ActorHeap.new(HeapConfig.small())
check(heap.config.initial_size.value == 512)
```

</details>

#### creates large heap

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = ActorHeap.new(HeapConfig.large())
check(heap.config.initial_size.value == 65536)
```

</details>

### ActorHeap - Allocation

#### allocates memory

1. var heap = ActorHeap new
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
val result = heap.allocate(100)

check(result.is_success())
```

</details>

#### tracks allocation stats

1. var heap = ActorHeap new
2. heap allocate
3. heap allocate
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(100)
heap.allocate(200)

val stats = heap.get_stats()
check(stats.used_bytes.value == 300)
check(stats.object_count.value == 2)
```

</details>

#### fails when heap exhausted

1. initial size: ByteSize
2. max size: ByteSize
3. var heap = ActorHeap new
4. heap allocate
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HeapConfig(
    initial_size: ByteSize(value: 100),
    max_size: ByteSize(value: 100),
    gc_enabled: false,
    generational: false,
    pretenure_threshold: 0
)
var heap = ActorHeap.new(config)

# Fill the heap
heap.allocate(90)

# Next allocation should fail
val result = heap.allocate(50)
check(not result.is_success())
```

</details>

#### handles zero-size allocation

1. var heap = ActorHeap new
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
val result = heap.allocate(0)

check(result.is_success())
```

</details>

### ActorHeap - Garbage Collection

#### triggers GC when threshold reached

1. var heap = ActorHeap new
2. heap allocate
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HeapConfig.default()
var heap = ActorHeap.new(config)

heap.allocate(200 * 1024)

val stats = heap.get_stats()
check(stats.allocated_bytes.value >= 0)
```

</details>

#### collects garbage manually

1. var heap = ActorHeap new
2. heap allocate
3. heap collect garbage
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(1000)

heap.collect_garbage()

val stats = heap.get_stats()
check(stats.gc_count.value >= 1)
```

</details>

#### collects young generation only

1. var heap = ActorHeap new
2. heap allocate
3. heap collect young generation
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(500)

heap.collect_young_generation()

val stats = heap.get_stats()
check(stats.young_gen_size.value >= 0)
```

</details>

#### respects gc_enabled flag

1. initial size: ByteSize
2. max size: ByteSize
3. var heap = ActorHeap new
4. heap collect garbage
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HeapConfig(
    initial_size: ByteSize(value: 1024),
    max_size: ByteSize(value: 4096),
    gc_enabled: false,
    generational: false,
    pretenure_threshold: 0
)
var heap = ActorHeap.new(config)

heap.collect_garbage()

val stats = heap.get_stats()
check(stats.gc_count.value == 0)
```

</details>

### ActorHeap - Statistics

#### tracks peak usage

1. var heap = ActorHeap new
2. heap allocate
3. heap allocate
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())

heap.allocate(100)
heap.allocate(200)

val stats = heap.get_stats()
check(stats.peak_used_bytes.value >= 300)
```

</details>

#### reports usage percent

1. var heap = ActorHeap new
2. heap allocate
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(100)

val usage = heap.usage_percent()
check(usage >= 0)
check(usage <= 100)
```

</details>

#### checks heap health

1. var heap = ActorHeap new
2. heap allocate
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(1000)

check(heap.is_healthy())
```

</details>

### ActorHeap - Display

#### formats heap for display

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = ActorHeap.new(HeapConfig.default())
val s = heap.fmt()

check(s.contains("ActorHeap"))
```

</details>

#### formats stats for display

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = HeapStats.new()
val s = stats.fmt()

check(s.contains("HeapStats"))
```

</details>

### ActorHeap - Region Management

#### tracks young generation

1. var heap = ActorHeap new
2. heap allocate
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(100)

check(heap.young_generation.used.value >= 100)
```

</details>

#### handles non-generational heap

1. var heap = ActorHeap new
2. heap allocate
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = HeapConfig.no_gc(1024)
var heap = ActorHeap.new(config)

heap.allocate(100)

check(not heap.has_old_generation)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/actor_heap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ActorHeap - Configuration
- ActorHeap - Allocation
- ActorHeap - Garbage Collection
- ActorHeap - Statistics
- ActorHeap - Display
- ActorHeap - Region Management

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
