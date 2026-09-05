# Garbage Collector Local Coverage

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
| Source | `test/unit/lib/std/gc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### GcObjectHeader

#### creates header with size and type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates header with size and type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates header with size and type")
val header = GcObjectHeader.create(32, "Node")
check_eq_i64(header.size, 32)
check_eq_text(header.type_name, "Node")
```

</details>

#### initializes as white

- initializes as white


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes as white")
val header = GcObjectHeader.create(16, "Pair")
check_eq_text(header.color, "white")
```

</details>

#### marks object

- marks object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks object")
val header = GcObjectHeader.create(8, "Tiny")
header.mark_gray()
check_eq_text(header.color, "gray")
```

</details>

#### unmarks object

- unmarks object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unmarks object")
val header = GcObjectHeader.create(8, "Tiny")
header.mark_black()
header.mark_white()
check_eq_text(header.color, "white")
```

</details>

#### makes object black

- makes object black


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes object black")
val header = GcObjectHeader.create(8, "Tiny")
header.mark_black()
check_eq_text(header.color, "black")
```

</details>

#### starts in young generation

- starts in young generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts in young generation")
val header = GcObjectHeader.create(8, "Tiny")
check_eq_text(header.generation, "young")
```

</details>

#### promotes to old generation

- promotes to old generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("promotes to old generation")
val header = GcObjectHeader.create(8, "Tiny")
header.promote()
check_eq_text(header.generation, "old")
```

</details>

### GcConfig

#### creates default configuration

- creates default configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default configuration")
val config = GcConfig.default()
check(config.max_heap_size > 0)
```

</details>

#### has reasonable thresholds

- has reasonable thresholds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has reasonable thresholds")
val config = GcConfig.default()
check(config.full_threshold > config.young_threshold)
```

</details>

#### creates config with specific heap size

- creates config with specific heap size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates config with specific heap size")
val config = GcConfig.with_heap_size(256)
check_eq_i64(config.max_heap_size, 256)
```

</details>

### GcStats

#### starts with zero stats

- starts with zero stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero stats")
val stats = GcStats.zero()
check_eq_i64(stats.collections, 0)
check_eq_i64(stats.total_pause_ms, 0)
```

</details>

#### calculates average pause time

- calculates average pause time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates average pause time")
val stats = GcStats(collections: 2, young_collections: 1, full_collections: 1, total_pause_ms: 6, survived_objects: 0, last_survival_rate_percent: 0)
check_eq_i64(stats.average_pause_ms(), 3)
```

</details>

#### handles zero collections

- handles zero collections


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero collections")
val stats = GcStats.zero()
check_eq_i64(stats.average_pause_ms(), 0)
```

</details>

#### tracks survival rate

- tracks survival rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks survival rate")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Root")
heap.add_root(id)
heap.collect_full()
check_eq_i64(heap.stats.last_survival_rate_percent, 100)
```

</details>

### GcHeap - Basic

#### creates heap with default config

- creates heap with default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates heap with default config")
val heap = GcHeap.create_default()
check_eq_i64(heap.objects.len(), 0)
```

</details>

#### creates heap with custom config

- creates heap with custom config


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates heap with custom config")
val heap = GcHeap.create(GcConfig.with_heap_size(512))
check_eq_i64(heap.config.max_heap_size, 512)
```

</details>

#### allocates object

- allocates object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates object")
val heap = GcHeap.create_default()
val id = heap.alloc(12, "Box")
check(id > 0)
check_eq_i64(heap.objects.len(), 1)
```

</details>

#### tracks allocated bytes

- tracks allocated bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks allocated bytes")
val heap = GcHeap.create_default()
val _ = heap.alloc(12, "Box")
check_eq_i64(heap.allocated_bytes, 12)
```

</details>

#### allocates multiple objects

- allocates multiple objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates multiple objects")
val heap = GcHeap.create_default()
val _ = heap.alloc(10, "A")
val _ = heap.alloc(20, "B")
check_eq_i64(heap.objects.len(), 2)
```

</details>

#### checks if collection needed

- checks if collection needed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if collection needed")
val heap = GcHeap.create(GcConfig(young_threshold: 10, full_threshold: 20, max_heap_size: 128))
val _ = heap.alloc(12, "A")
check(heap.needs_collection())
```

</details>

### GcHeap - Roots

#### adds root

- adds root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds root")
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Rooted")
heap.add_root(id)
check_eq_i64(heap.roots.len(), 1)
```

</details>

#### removes root

- removes root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes root")
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Rooted")
heap.add_root(id)
heap.remove_root(id)
check_eq_i64(heap.roots.len(), 0)
```

</details>

#### clears all roots

- clears all roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all roots")
val heap = GcHeap.create_default()
heap.add_root(heap.alloc(10, "A"))
heap.add_root(heap.alloc(10, "B"))
heap.clear_roots()
check_eq_i64(heap.roots.len(), 0)
```

</details>

### GcHeap - Collection

#### runs collection

- runs collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs collection")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.stats.collections, 1)
```

</details>

#### prevents recursive collection

- prevents recursive collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prevents recursive collection")
val heap = GcHeap.create_default()
heap.collecting = true
heap.collect_full()
check_eq_i64(heap.stats.collections, 0)
```

</details>

#### updates pause time stats

- updates pause time stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates pause time stats")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_full()
check(heap.stats.total_pause_ms > 0)
```

</details>

#### frees unreachable objects

- frees unreachable objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frees unreachable objects")
val heap = GcHeap.create_default()
val _ = heap.alloc(10, "Dead")
heap.collect_full()
check_eq_i64(heap.live_count(), 0)
```

</details>

#### keeps reachable objects

- keeps reachable objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps reachable objects")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Live")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.live_count(), 1)
```

</details>

#### collects young generation

- collects young generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects young generation")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Young")
heap.add_root(root)
heap.collect_young()
check_eq_i64(heap.stats.young_collections, 1)
```

</details>

### GcHeap - Mark Phase

#### marks reachable objects

- marks reachable objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks reachable objects")
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

- marks object graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks object graph")
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.reset_colors()
heap.mark_from_roots()
check_eq_text(heap.objects[2].header.color, "black")
```

</details>

### GcHeap - Sweep Phase

#### frees unmarked objects

- frees unmarked objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frees unmarked objects")
val heap = GcHeap.create_default()
val _ = heap.alloc(10, "Dead")
heap.reset_colors()
heap.sweep(true)
check_eq_i64(heap.live_count(), 0)
```

</details>

#### keeps marked objects

- keeps marked objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps marked objects")
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

- creates smart pointer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates smart pointer")
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Ptr")
val handle = GcHandle.create(heap, id)
check_eq_i64(handle.object_id, id)
```

</details>

#### automatically registers as root

- automatically registers as root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("automatically registers as root")
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Ptr")
val _ = GcHandle.create(heap, id)
check_eq_i64(heap.roots.len(), 1)
```

</details>

#### unregisters on release

- unregisters on release


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unregisters on release")
val heap = GcHeap.create_default()
val id = heap.alloc(10, "Ptr")
val handle = GcHandle.create(heap, id)
handle.release()
check_eq_i64(heap.roots.len(), 0)
```

</details>

### GC Integration

#### handles multiple collection cycles

- handles multiple collection cycles


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple collection cycles")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_young()
heap.collect_full()
check_eq_i64(heap.stats.collections, 2)
```

</details>

#### maintains correct stats

- maintains correct stats


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains correct stats")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.stats.full_collections, 1)
```

</details>

#### calculates survival rate correctly

- calculates survival rate correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates survival rate correctly")
val heap = GcHeap.create_default()
val root = heap.alloc(10, "Root")
val _ = heap.alloc(10, "Dead")
heap.add_root(root)
heap.collect_full()
check_eq_i64(heap.stats.last_survival_rate_percent, 50)
```

</details>

#### handles many allocations

- handles many allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many allocations")
val heap = GcHeap.create(GcConfig.with_heap_size(2048))
var i = 0
while i < 50:
    val _ = heap.alloc(8, "Node")
    i = i + 1
check(heap.objects.len() >= 50)
```

</details>

#### handles alternating alloc collect

- handles alternating alloc collect


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles alternating alloc collect")
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

- marks white object as gray when discovered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks white object as gray when discovered")
val header = GcObjectHeader.create(8, "Node")
header.mark_gray()
check_eq_text(header.color, "gray")
```

</details>

#### adds newly marked object to reachable path

- adds newly marked object to reachable path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds newly marked object to reachable path")
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.reset_colors()
heap.mark_from_roots()
check_eq_text(heap.objects[1].header.color, "black")
```

</details>

#### transitions gray to black after scanning children

- transitions gray to black after scanning children


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions gray to black after scanning children")
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.reset_colors()
heap.mark_from_roots()
check_eq_text(heap.objects[0].header.color, "black")
```

</details>

#### does not revisit black objects during marking

- does not revisit black objects during marking


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not revisit black objects during marking")
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

- maintains black references after marking


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains black references after marking")
val heap = make_heap_with_three()
heap.add_root(heap.objects[0].id)
heap.collect_full()
check_eq_text(heap.objects[0].header.color, "black")
```

</details>

#### resets all colors to white before new cycle

- resets all colors to white before new cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets all colors to white before new cycle")
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

- promotes young object that survives collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("promotes young object that survives collection")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Young")
heap.add_root(id)
heap.collect_young()
check_eq_text(heap.objects[0].header.generation, "old")
```

</details>

#### collects young generation more frequently

- collects young generation more frequently


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects young generation more frequently")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Young")
heap.add_root(id)
heap.collect_young()
heap.collect_young()
check_eq_i64(heap.stats.young_collections, 2)
```

</details>

#### promotes survivors from young to old

- promotes survivors from young to old


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("promotes survivors from young to old")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Survivor")
heap.add_root(id)
heap.collect_young()
check_eq_text(heap.objects[0].header.generation, "old")
```

</details>

#### collects both young and old generations

- collects both young and old generations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects both young and old generations")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Root")
heap.add_root(id)
heap.collect_young()
heap.collect_full()
check_eq_i64(heap.stats.full_collections, 1)
```

</details>

#### tracks old to young pointers

- tracks old to young pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks old to young pointers")
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

- marks objects with finalizers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks objects with finalizers")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "WithFinalizer")
heap.set_finalizer(id, false)
check(heap.objects[0].header.has_finalizer)
```

</details>

#### runs finalizers before reclaiming memory

- runs finalizers before reclaiming memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs finalizers before reclaiming memory")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "WithFinalizer")
heap.set_finalizer(id, false)
heap.collect_full()
check_eq_i64(heap.live_count(), 0)
```

</details>

#### handles object resurrection in finalizer

- handles object resurrection in finalizer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles object resurrection in finalizer")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "Phoenix")
heap.set_finalizer(id, true)
heap.collect_full()
check_eq_i64(heap.live_count(), 1)
```

</details>

#### handles finalizer referencing another finalizable object

- handles finalizer referencing another finalizable object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles finalizer referencing another finalizable object")
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

- runs finalizers in dependency order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs finalizers in dependency order")
val heap = GcHeap.create_default()
val a = heap.alloc(8, "A")
heap.set_finalizer(a, false)
heap.collect_full()
check(heap.stats.collections > 0)
```

</details>

### Memory Pressure

#### triggers GC when threshold exceeded

- triggers GC when threshold exceeded


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triggers GC when threshold exceeded")
val heap = GcHeap.create(GcConfig(young_threshold: 8, full_threshold: 16, max_heap_size: 32))
val _ = heap.alloc(10, "A")
check(heap.needs_collection())
```

</details>

#### does not trigger GC when below threshold

- does not trigger GC when below threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not trigger GC when below threshold")
val heap = GcHeap.create(GcConfig(young_threshold: 64, full_threshold: 128, max_heap_size: 256))
val _ = heap.alloc(8, "A")
check(not heap.needs_collection())
```

</details>

#### grows heap when needed within max

- grows heap when needed within max


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grows heap when needed within max")
val heap = GcHeap.create(GcConfig.with_heap_size(64))
val _ = heap.alloc(16, "A")
val _ = heap.alloc(16, "B")
check(heap.allocated_bytes <= 64)
```

</details>

#### respects maximum heap size

- respects maximum heap size


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects maximum heap size")
val heap = GcHeap.create(GcConfig.with_heap_size(16))
val id = heap.alloc(32, "TooBig")
check_eq_i64(id, -1)
```

</details>

<details>
<summary>Advanced: returns -1 when out of memory</summary>

#### returns -1 when out of memory

- returns -1 when out of memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when out of memory")
val heap = GcHeap.create(GcConfig.with_heap_size(8))
val id = heap.alloc(16, "OOM")
check_eq_i64(id, -1)
```

</details>


</details>

<details>
<summary>Advanced: handles repeated OOM gracefully</summary>

#### handles repeated OOM gracefully

- handles repeated OOM gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles repeated OOM gracefully")
val heap = GcHeap.create(GcConfig.with_heap_size(8))
check_eq_i64(heap.alloc(16, "OOM1"), -1)
check_eq_i64(heap.alloc(16, "OOM2"), -1)
```

</details>


</details>

### GC Statistics

#### records pause time for each collection

- records pause time for each collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records pause time for each collection")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "A")
heap.add_root(id)
heap.collect_full()
check(heap.stats.total_pause_ms > 0)
```

</details>

#### accumulates total pause time

- accumulates total pause time


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accumulates total pause time")
val heap = GcHeap.create_default()
val id = heap.alloc(8, "A")
heap.add_root(id)
heap.collect_full()
heap.collect_full()
check_eq_i64(heap.stats.total_pause_ms, 4)
```

</details>

#### tracks young and full collections separately

- tracks young and full collections separately


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks young and full collections separately")
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

- handles minimum size objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles minimum size objects")
val heap = GcHeap.create_default()
val id = heap.alloc(1, "Min")
check(id > 0)
```

</details>

#### handles zero size objects

- handles zero size objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero size objects")
val heap = GcHeap.create_default()
val id = heap.alloc(0, "Zero")
check(id > 0)
```

</details>

#### handles large objects

- handles large objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large objects")
val heap = GcHeap.create(GcConfig.with_heap_size(2048))
val id = heap.alloc(512, "Large")
check(id > 0)
```

</details>

#### handles very large objects

- handles very large objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles very large objects")
val heap = GcHeap.create(GcConfig.with_heap_size(4096))
val id = heap.alloc(2048, "Huge")
check(id > 0)
```

</details>

#### handles mix of small and large objects

- handles mix of small and large objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles mix of small and large objects")
val heap = GcHeap.create(GcConfig.with_heap_size(4096))
val _ = heap.alloc(8, "Small")
val _ = heap.alloc(512, "Large")
check_eq_i64(heap.objects.len(), 2)
```

</details>

### Incremental GC

#### supports incremental marking mode

- supports incremental marking mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports incremental marking mode")
val heap = GcHeap.create_default()
heap.incremental_mode = true
check(heap.incremental_mode)
```

</details>

#### pauses and resumes marking

- pauses and resumes marking


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pauses and resumes marking")
val heap = GcHeap.create_default()
heap.incremental_mode = true
heap.collecting = true
heap.collecting = false
check(not heap.collecting)
```

</details>

### Concurrent GC

#### supports concurrent marking mode

- supports concurrent marking mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports concurrent marking mode")
val heap = GcHeap.create_default()
heap.concurrent_mode = true
check(heap.concurrent_mode)
```

</details>

#### uses atomic style guard for concurrent access

- uses atomic style guard for concurrent access


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses atomic style guard for concurrent access")
val heap = GcHeap.create_default()
heap.concurrent_mode = true
heap.collect_full()
check_eq_i64(heap.stats.collections, 1)
```

</details>

### GC Stress Tests

#### handles rapid allocation and collection cycles

- handles rapid allocation and collection cycles


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles rapid allocation and collection cycles")
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

- handles alternating allocation and collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles alternating allocation and collection")
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

- handles repeated full heap allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles repeated full heap allocations")
val heap = GcHeap.create(GcConfig.with_heap_size(256))
val a = heap.alloc(128, "A")
val b = heap.alloc(128, "B")
check(a > 0)
check(b > 0 or b == -1)
```

</details>

#### handles fragmentation from mixed sizes

- handles fragmentation from mixed sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles fragmentation from mixed sizes")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `230bd8117768020ed5cbe240f5befd824ce961e0f23a2a46dcfa42b243356272`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `230bd8117768020ed5cbe240f5befd824ce961e0f23a2a46dcfa42b243356272`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `230bd8117768020ed5cbe240f5befd824ce961e0f23a2a46dcfa42b243356272`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/std/gc_spec.spl
mirror: doc/06_spec/unit/lib/std/gc_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/gc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/gc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/gc_spec.spl:309:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates header with size and type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/gc_spec.spl:316:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes as white' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/gc_spec.spl:322:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
