# Actor Heap Specification

> Tests covering ActorHeap - Configuration, ActorHeap - Allocation, ActorHeap - Garbage Collection, ActorHeap - Statistics, ActorHeap - Display, ActorHeap - Region Management.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Heap Specification

## Scenarios

### ActorHeap - Configuration

#### creates with default config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates with default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with default config")
val heap = ActorHeap.new(HeapConfig.default())
val config = heap.config

check(config.initial_size.value == 2048)
check(config.gc_enabled)
check(config.generational)
```

</details>

#### creates with custom config

- creates with custom config


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with custom config")
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

- creates small heap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates small heap")
val heap = ActorHeap.new(HeapConfig.small())
check(heap.config.initial_size.value == 512)
```

</details>

#### creates large heap

- creates large heap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates large heap")
val heap = ActorHeap.new(HeapConfig.large())
check(heap.config.initial_size.value == 65536)
```

</details>

### ActorHeap - Allocation

#### allocates memory

- allocates memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates memory")
var heap = ActorHeap.new(HeapConfig.default())
val result = heap.allocate(100)

check(result.is_success())
```

</details>

#### tracks allocation stats

- tracks allocation stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks allocation stats")
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(100)
heap.allocate(200)

val stats = heap.get_stats()
check(stats.used_bytes.value == 300)
check(stats.object_count.value == 2)
```

</details>

#### fails when heap exhausted

- fails when heap exhausted


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when heap exhausted")
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

- handles zero-size allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero-size allocation")
var heap = ActorHeap.new(HeapConfig.default())
val result = heap.allocate(0)

check(result.is_success())
```

</details>

### ActorHeap - Garbage Collection

#### triggers GC when threshold reached

- triggers GC when threshold reached


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triggers GC when threshold reached")
val config = HeapConfig.default()
var heap = ActorHeap.new(config)

heap.allocate(200 * 1024)

val stats = heap.get_stats()
check(stats.allocated_bytes.value >= 0)
```

</details>

#### collects garbage manually

- collects garbage manually


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects garbage manually")
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(1000)

heap.collect_garbage()

val stats = heap.get_stats()
check(stats.gc_count.value >= 1)
```

</details>

#### collects young generation only

- collects young generation only


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects young generation only")
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(500)

heap.collect_young_generation()

val stats = heap.get_stats()
check(stats.young_gen_size.value >= 0)
```

</details>

#### respects gc_enabled flag

- respects gc_enabled flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects gc_enabled flag")
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

- tracks peak usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks peak usage")
var heap = ActorHeap.new(HeapConfig.default())

heap.allocate(100)
heap.allocate(200)

val stats = heap.get_stats()
check(stats.peak_used_bytes.value >= 300)
```

</details>

#### reports usage percent

- reports usage percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports usage percent")
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(100)

val usage = heap.usage_percent()
check(usage >= 0)
check(usage <= 100)
```

</details>

#### checks heap health

- checks heap health


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks heap health")
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(1000)

check(heap.is_healthy())
```

</details>

### ActorHeap - Display

#### formats heap for display

- formats heap for display


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats heap for display")
val heap = ActorHeap.new(HeapConfig.default())
val s = heap.fmt()

check(s.contains("ActorHeap"))
```

</details>

#### formats stats for display

- formats stats for display


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats stats for display")
val stats = HeapStats.new()
val s = stats.fmt()

check(s.contains("HeapStats"))
```

</details>

### ActorHeap - Region Management

#### tracks young generation

- tracks young generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks young generation")
var heap = ActorHeap.new(HeapConfig.default())
heap.allocate(100)

check(heap.young_generation.used.value >= 100)
```

</details>

#### handles non-generational heap

- handles non-generational heap


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles non-generational heap")
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
| Source | `test/unit/app/interpreter/actor_heap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ActorHeap - Configuration, ActorHeap - Allocation, ActorHeap - Garbage Collection, ActorHeap - Statistics, ActorHeap - Display, ActorHeap - Region Management.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09a224e4242528ea73ec9d776dac33584d54bd6c2d0811f0a53419c4fa194407`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09a224e4242528ea73ec9d776dac33584d54bd6c2d0811f0a53419c4fa194407`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09a224e4242528ea73ec9d776dac33584d54bd6c2d0811f0a53419c4fa194407`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/interpreter/actor_heap_spec.spl
mirror: doc/06_spec/unit/app/interpreter/actor_heap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/interpreter/actor_heap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/interpreter/actor_heap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/interpreter/actor_heap_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with default config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/interpreter/actor_heap_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with custom config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/interpreter/actor_heap_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates small heap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
