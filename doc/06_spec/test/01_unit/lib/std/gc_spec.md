# Garbage Collector Local Coverage

> 1. check eq i64

<!-- sdn-diagram:id=gc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 79 | 79 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Garbage Collector Local Coverage

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/gc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### GcObjectHeader

#### creates header with size and type

1. check eq i64
2. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(32, "Node")
check_eq_i64(header.size, 32)
check_eq_text(header.type_name, "Node")
```

</details>

#### initializes as white

1. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(16, "Pair")
check_eq_text(header.color, "white")
```

</details>

#### marks object

1. header mark gray
2. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(8, "Tiny")
header.mark_gray()
check_eq_text(header.color, "gray")
```

</details>

#### unmarks object

1. header mark black
2. header mark white
3. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(8, "Tiny")
header.mark_black()
header.mark_white()
check_eq_text(header.color, "white")
```

</details>

#### makes object black

1. header mark black
2. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(8, "Tiny")
header.mark_black()
check_eq_text(header.color, "black")
```

</details>

#### starts in young generation

1. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(8, "Tiny")
check_eq_text(header.generation, "young")
```

</details>

#### promotes to old generation

1. header promote
2. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(8, "Tiny")
header.promote()
check_eq_text(header.generation, "old")
```

</details>

### GcConfig

#### creates default configuration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GcConfig.default()
check(config.max_heap_size > 0)
```

</details>

#### has reasonable thresholds

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GcConfig.default()
check(config.full_threshold > config.young_threshold)
```

</details>

#### creates config with specific heap size

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GcConfig.with_heap_size(256)
check_eq_i64(config.max_heap_size, 256)
```

</details>

### GcStats

#### starts with zero stats

1. check eq i64
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = GcStats.zero()
check_eq_i64(stats.collections, 0)
check_eq_i64(stats.total_pause_ms, 0)
```

</details>

#### calculates average pause time

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = GcStats(collections: 2, young_collections: 1, full_collections: 1, total_pause_ms: 6, survived_objects: 0, last_survival_rate_percent: 0)
check_eq_i64(stats.average_pause_ms(), 3)
```

</details>

#### handles zero collections

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = GcStats.zero()
check_eq_i64(stats.average_pause_ms(), 0)
```

</details>

#### tracks survival rate

1. heap add root
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Root")
heap.add_root(id)
heap.collect_full()
check_eq_i64(heap.stats.last_survival_rate_percent, 100)
```

</details>

### GcHeap - Basic

#### creates heap with default config

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
check_eq_i64(heap.objects.len(), 0)
```

</details>

#### creates heap with custom config

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(512))
check_eq_i64(heap.config.max_heap_size, 512)
```

</details>

#### allocates object

1. check
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(12, "Box")
check(id > 0)
check_eq_i64(heap.objects.len(), 1)
```

</details>

#### tracks allocated bytes

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val _ = heap.alloc(12, "Box")
check_eq_i64(heap.allocated_bytes, 12)
```

</details>

#### allocates multiple objects

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val _ = heap.alloc(10, "A")
val _ = heap.alloc(20, "B")
check_eq_i64(heap.objects.len(), 2)
```

</details>

#### checks if collection needed

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig(young_threshold: 10, full_threshold: 20, max_heap_size: 128))
val _ = heap.alloc(12, "A")
check(heap.needs_collection())
```

</details>

### GcHeap - Roots

#### adds root

1. heap add root
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Rooted")
heap.add_root(id)
check_eq_i64(heap.roots.len(), 1)
```

</details>

#### removes root

1. heap add root
2. heap remove root
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Rooted")
heap.add_root(id)
heap.remove_root(id)
check_eq_i64(heap.roots.len(), 0)
```

</details>

#### clears all roots

1. heap add root
2. heap add root
3. heap clear roots
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
heap.add_root(heap.alloc(10, "A"))
heap.add_root(heap.alloc(10, "B"))
heap.clear_roots()
check_eq_i64(heap.roots.len(), 0)
```

</details>

### GcHeap - Collection

#### runs collection

1. heap add root
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.stats.collections, 1)
```

</details>

#### prevents recursive collection

1. heap collect full
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
heap.collecting = true
heap.collect_full()
check_eq_i64(heap.stats.collections, 0)
```

</details>

#### updates pause time stats

1. heap add root
2. heap collect full
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_full()
check(heap.stats.total_pause_ms > 0)
```

</details>

#### frees unreachable objects

1. heap collect full
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val _ = heap.alloc(10, "Dead")
heap.collect_full()
check_eq_i64(heap.live_count(), 0)
```

</details>

#### keeps reachable objects

1. heap add root
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Live")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.live_count(), 1)
```

</details>

#### collects young generation

1. heap add root
2. heap collect young
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Young")
heap.add_root(root)
heap.collect_young()
check_eq_i64(heap.stats.young_collections, 1)
```

</details>

### GcHeap - Mark Phase

#### marks reachable objects

1. heap add root
2. heap reset colors
3. heap mark from roots
4. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.reset_colors()
heap.mark_from_roots()
val idx = heap.find_index(root)
check_eq_text(heap.objects[idx].header.color, "black")
```

</details>

#### marks object graph

1. heap add root
2. heap reset colors
3. heap mark from roots
4. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.reset_colors()
heap.mark_from_roots()
check_eq_text(heap.objects[2].header.color, "black")
```

</details>

### GcHeap - Sweep Phase

#### frees unmarked objects

1. heap reset colors
2. heap sweep
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val _ = heap.alloc(10, "Dead")
heap.reset_colors()
heap.sweep(true)
check_eq_i64(heap.live_count(), 0)
```

</details>

#### keeps marked objects

1. heap add root
2. heap reset colors
3. heap mark from roots
4. heap sweep
5. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Live")
heap.add_root(root)
heap.reset_colors()
heap.mark_from_roots()
heap.sweep(true)
check_eq_i64(heap.live_count(), 1)
```

</details>

### GcPtr

#### creates smart pointer

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Ptr")
val handle = GcHandle.create(heap, id)
check_eq_i64(handle.object_id, id)
```

</details>

#### automatically registers as root

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Ptr")
val _ = GcHandle.create(heap, id)
check_eq_i64(heap.roots.len(), 1)
```

</details>

#### unregisters on release

1. handle release
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Ptr")
val handle = GcHandle.create(heap, id)
handle.release()
check_eq_i64(heap.roots.len(), 0)
```

</details>

### GC Integration

#### handles multiple collection cycles

1. heap add root
2. heap collect young
3. heap collect full
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_young()
heap.collect_full()
check_eq_i64(heap.stats.collections, 2)
```

</details>

#### maintains correct stats

1. heap add root
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.stats.full_collections, 1)
```

</details>

#### calculates survival rate correctly

1. heap add root
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
val _ = heap.alloc(10, "Dead")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.stats.last_survival_rate_percent, 50)
```

</details>

#### handles many allocations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(2048))
var i = 0
while i < 50:
    val _ = heap.alloc(8, "Node")
    i = i + 1
check(heap.objects.len() >= 50)
```

</details>

#### handles alternating alloc collect

1. heap add root
2. heap collect full
3. heap remove root
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
var i = 0
while i < 5:
    val id = heap.alloc(8, "Tmp")
    heap.add_root(id)
    heap.collect_full()
    heap.remove_root(id)
    i = i + 1
check_eq_i64(heap.stats.collections, 5)
```

</details>

### Tri-Color Marking Transitions

#### marks white object as gray when discovered

1. header mark gray
2. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = GcObjectHeader.create(8, "Node")
header.mark_gray()
check_eq_text(header.color, "gray")
```

</details>

#### adds newly marked object to reachable path

1. heap add root
2. heap reset colors
3. heap mark from roots
4. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.reset_colors()
heap.mark_from_roots()
check_eq_text(heap.objects[1].header.color, "black")
```

</details>

#### transitions gray to black after scanning children

1. heap add root
2. heap reset colors
3. heap mark from roots
4. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.reset_colors()
heap.mark_from_roots()
check_eq_text(heap.objects[0].header.color, "black")
```

</details>

#### does not revisit black objects during marking

1. heap add root
2. heap mark reachable
3. heap mark reachable
4. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Node")
heap.add_root(id)
heap.mark_reachable(id)
val before = heap.objects[0].header.color
heap.mark_reachable(id)
check_eq_text(heap.objects[0].header.color, before)
```

</details>

#### maintains black references after marking

1. heap add root
2. heap collect full
3. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.collect_full()
check_eq_text(heap.objects[0].header.color, "black")
```

</details>

#### resets all colors to white before new cycle

1. heap add root
2. heap collect full
3. heap reset colors
4. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Node")
heap.add_root(id)
heap.collect_full()
heap.reset_colors()
check_eq_text(heap.objects[0].header.color, "white")
```

</details>

### Generational Collection

#### promotes young object that survives collection

1. heap add root
2. heap collect young
3. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Young")
heap.add_root(id)
heap.collect_young()
check_eq_text(heap.objects[0].header.generation, "old")
```

</details>

#### collects young generation more frequently

1. heap add root
2. heap collect young
3. heap collect young
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Young")
heap.add_root(id)
heap.collect_young()
heap.collect_young()
check_eq_i64(heap.stats.young_collections, 2)
```

</details>

#### promotes survivors from young to old

1. heap add root
2. heap collect young
3. check eq text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Survivor")
heap.add_root(id)
heap.collect_young()
check_eq_text(heap.objects[0].header.generation, "old")
```

</details>

#### collects both young and old generations

1. heap add root
2. heap collect young
3. heap collect full
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Root")
heap.add_root(id)
heap.collect_young()
heap.collect_full()
check_eq_i64(heap.stats.full_collections, 1)
```

</details>

#### tracks old to young pointers

1. heap add root
2. heap collect young
3. heap add ref
4. heap collect full
5. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val parent = heap.alloc(8, "Parent")
val child = heap.alloc(8, "Child")
heap.add_root(parent)
heap.collect_young()
heap.add_ref(parent, child)
heap.collect_full()
check_eq_i64(heap.live_count(), 2)
```

</details>

### Finalization

#### marks objects with finalizers

1. heap set finalizer
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "WithFinalizer")
heap.set_finalizer(id, false)
check(heap.objects[0].header.has_finalizer)
```

</details>

#### runs finalizers before reclaiming memory

1. heap set finalizer
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "WithFinalizer")
heap.set_finalizer(id, false)
heap.collect_full()
check_eq_i64(heap.live_count(), 0)
```

</details>

#### handles object resurrection in finalizer

1. heap set finalizer
2. heap collect full
3. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Phoenix")
heap.set_finalizer(id, true)
heap.collect_full()
check_eq_i64(heap.live_count(), 1)
```

</details>

#### handles finalizer referencing another finalizable object

1. heap add ref
2. heap set finalizer
3. heap set finalizer
4. heap collect full
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val a = heap.alloc(8, "A")
val b = heap.alloc(8, "B")
heap.add_ref(a, b)
heap.set_finalizer(a, true)
heap.set_finalizer(b, false)
heap.collect_full()
check(heap.live_count() >= 1)
```

</details>

#### runs finalizers in dependency order

1. heap set finalizer
2. heap collect full
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val a = heap.alloc(8, "A")
heap.set_finalizer(a, false)
heap.collect_full()
check(heap.stats.collections > 0)
```

</details>

### Memory Pressure

#### triggers GC when threshold exceeded

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig(young_threshold: 8, full_threshold: 16, max_heap_size: 32))
val _ = heap.alloc(10, "A")
check(heap.needs_collection())
```

</details>

#### does not trigger GC when below threshold

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig(young_threshold: 64, full_threshold: 128, max_heap_size: 256))
val _ = heap.alloc(8, "A")
check(not heap.needs_collection())
```

</details>

#### grows heap when needed within max

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(64))
val _ = heap.alloc(16, "A")
val _ = heap.alloc(16, "B")
check(heap.allocated_bytes <= 64)
```

</details>

#### respects maximum heap size

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(16))
val id = heap.alloc(32, "TooBig")
check_eq_i64(id, -1)
```

</details>

<details>
<summary>Advanced: returns -1 when out of memory</summary>

#### returns -1 when out of memory

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(8))
val id = heap.alloc(16, "OOM")
check_eq_i64(id, -1)
```

</details>


</details>

<details>
<summary>Advanced: handles repeated OOM gracefully</summary>

#### handles repeated OOM gracefully

1. check eq i64
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(8))
check_eq_i64(heap.alloc(16, "OOM1"), -1)
check_eq_i64(heap.alloc(16, "OOM2"), -1)
```

</details>


</details>

### GC Statistics

#### records pause time for each collection

1. heap add root
2. heap collect full
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "A")
heap.add_root(id)
heap.collect_full()
check(heap.stats.total_pause_ms > 0)
```

</details>

#### accumulates total pause time

1. heap add root
2. heap collect full
3. heap collect full
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "A")
heap.add_root(id)
heap.collect_full()
heap.collect_full()
check_eq_i64(heap.stats.total_pause_ms, 4)
```

</details>

#### tracks young and full collections separately

1. heap add root
2. heap collect young
3. heap collect full
4. check eq i64
5. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(8, "A")
heap.add_root(id)
heap.collect_young()
heap.collect_full()
check_eq_i64(heap.stats.young_collections, 1)
check_eq_i64(heap.stats.full_collections, 1)
```

</details>

### Object Size Edge Cases

#### handles minimum size objects

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(1, "Min")
check(id > 0)
```

</details>

#### handles zero size objects

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
val id = heap.alloc(0, "Zero")
check(id > 0)
```

</details>

#### handles large objects

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(2048))
val id = heap.alloc(512, "Large")
check(id > 0)
```

</details>

#### handles very large objects

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(4096))
val id = heap.alloc(2048, "Huge")
check(id > 0)
```

</details>

#### handles mix of small and large objects

1. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(4096))
val _ = heap.alloc(8, "Small")
val _ = heap.alloc(512, "Large")
check_eq_i64(heap.objects.len(), 2)
```

</details>

### Incremental GC

#### supports incremental marking mode

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
heap.incremental_mode = true
check(heap.incremental_mode)
```

</details>

#### pauses and resumes marking

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
heap.incremental_mode = true
heap.collecting = true
heap.collecting = false
check(not heap.collecting)
```

</details>

### Concurrent GC

#### supports concurrent marking mode

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
heap.concurrent_mode = true
check(heap.concurrent_mode)
```

</details>

#### uses atomic style guard for concurrent access

1. heap collect full
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create_default()
heap.concurrent_mode = true
heap.collect_full()
check_eq_i64(heap.stats.collections, 1)
```

</details>

### GC Stress Tests

#### handles rapid allocation and collection cycles

1. heap add root
2. heap collect full
3. heap remove root
4. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(512))
var i = 0
while i < 10:
    val id = heap.alloc(8, "Node")
    heap.add_root(id)
    heap.collect_full()
    heap.remove_root(id)
    i = i + 1
check_eq_i64(heap.stats.collections, 10)
```

</details>

#### handles alternating allocation and collection

1. heap collect full
2. check eq i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(256))
var i = 0
while i < 5:
    val _ = heap.alloc(8, "Temp")
    heap.collect_full()
    i = i + 1
check_eq_i64(heap.stats.collections, 5)
```

</details>

#### handles repeated full heap allocations

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(256))
val a = heap.alloc(128, "A")
val b = heap.alloc(128, "B")
check(a > 0)
check(b > 0 or b == -1)
```

</details>

#### handles fragmentation from mixed sizes

1. heap collect full
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val heap = GcHeap.create(GcConfig.with_heap_size(1024))
val _ = heap.alloc(8, "A")
val _ = heap.alloc(64, "B")
val _ = heap.alloc(16, "C")
heap.collect_full()
check(heap.allocated_bytes >= 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 79 |
| Active scenarios | 79 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
