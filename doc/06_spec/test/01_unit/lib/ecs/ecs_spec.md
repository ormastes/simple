# ECS Stdlib Specification

> Verifies the ECS primitives (`Entity`, `EntityAllocator`, `ComponentStore<T>`,

<!-- sdn-diagram:id=ecs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ecs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ecs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ecs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ECS Stdlib Specification

Verifies the ECS primitives (`Entity`, `EntityAllocator`, `ComponentStore<T>`,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MDSOC-PLUS-ECS-STDLIB |
| Category | Library / Architecture |
| Status | In Progress |
| Source | `test/01_unit/lib/ecs/ecs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the ECS primitives (`Entity`, `EntityAllocator`, `ComponentStore<T>`,
`WorldBase`, `Scheduler`, `ChangeTracker`) introduced for MDSOC+ userland
services. These types are the shared building blocks for per-service Worlds.

## Scenarios

### ECS Entity allocator
_Generational indices, free-list reuse, staleness detection._

#### allocates distinct entities

1. var alloc = EntityAllocator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
val a = alloc.alloc()
val b = alloc.alloc()
expect a.id.to_equal(0)
expect b.id.to_equal(1)
expect alloc.len().to_equal(2)
```

</details>

#### reports null entity as not live

1. var alloc = EntityAllocator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
val n = Entity.null()
expect n.is_null().to_equal(true)
expect alloc.is_live(n).to_equal(false)
```

</details>

#### bumps generation on reuse so stale handles do not alias

1. var alloc = EntityAllocator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
val a = alloc.alloc()
val freed = alloc.free(a)
val b = alloc.alloc()
expect freed.to_equal(true)
expect b.id.to_equal(a.id)
expect alloc.is_live(a).to_equal(false)
expect alloc.is_live(b).to_equal(true)
```

</details>

#### rejects double-free of stale handles

1. var alloc = EntityAllocator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
val a = alloc.alloc()
val first = alloc.free(a)
val second = alloc.free(a)
expect first.to_equal(true)
expect second.to_equal(false)
```

</details>

### ECS ComponentStore
_Sparse-set insert / remove / contains with tick stamping._

#### inserts and reads back a component

1. var alloc = EntityAllocator new
2. var store: ComponentStore<Position> = ComponentStore new


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
var store: ComponentStore<Position> = ComponentStore.new()
val e = alloc.alloc()
val inserted = store.insert(e, Position(x: 3, y: 4), 1)
expect inserted.to_equal(true)
expect store.contains(e).to_equal(true)
expect store.len().to_equal(1)
```

</details>

#### remove uses swap-with-last to keep dense packed

1. var alloc = EntityAllocator new
2. var store: ComponentStore<Position> = ComponentStore new
3. store insert
4. store insert
5. store insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
var store: ComponentStore<Position> = ComponentStore.new()
val a = alloc.alloc()
val b = alloc.alloc()
val c = alloc.alloc()
store.insert(a, Position(x: 1, y: 1), 1)
store.insert(b, Position(x: 2, y: 2), 1)
store.insert(c, Position(x: 3, y: 3), 1)
val removed = store.remove(b)
expect removed.to_equal(true)
expect store.len().to_equal(2)
expect store.contains(a).to_equal(true)
expect store.contains(b).to_equal(false)
expect store.contains(c).to_equal(true)
```

</details>

#### records last-modified tick on insert and touch

1. var alloc = EntityAllocator new
2. var store: ComponentStore<Position> = ComponentStore new
3. store insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = EntityAllocator.new()
var store: ComponentStore<Position> = ComponentStore.new()
val e = alloc.alloc()
store.insert(e, Position(x: 0, y: 0), 5)
val slot = store.get_slot(e)
val tick_before = store.tick_at(slot)
val touched = store.touch(e, 9)
val tick_after = store.tick_at(slot)
expect tick_before.to_equal(5)
expect touched.to_equal(true)
expect tick_after.to_equal(9)
```

</details>

### ECS ChangeTracker
_Per-system bookmark that drives Added / Changed / Removed._

#### marks a slot as changed when its tick exceeds the bookmark

1. var t = ChangeTracker new
2. t bookmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = ChangeTracker.new()
t.bookmark(5)
val changed = t.is_changed_since(7)
val unchanged = t.is_changed_since(5)
expect changed.to_equal(true)
expect unchanged.to_equal(false)
```

</details>

#### drains removed events and leaves queue empty

1. var t = ChangeTracker new
2. t push removed
3. t push removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = ChangeTracker.new()
t.push_removed(Entity(id: 1, generation: 1), 2)
t.push_removed(Entity(id: 2, generation: 1), 3)
val drained = t.drain_removed()
val empty_again = t.drain_removed()
expect drained.len().to_equal(2)
expect empty_again.len().to_equal(0)
```

</details>

### ECS Scheduler
_Insertion-order systems, enable/disable flag, monotonic tick._

#### advances tick on each step

1. var s = Scheduler new
2. s step
3. s step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Scheduler.new()
val before = s.now()
s.step(0)
s.step(0)
val after = s.now()
expect before.to_equal(0)
expect after.to_equal(2)
```

</details>

### ECS WorldBase
_Shared base used by service Worlds (PM, VFS, WM)._

#### composes an EntityAllocator + Scheduler + tick counter

1. var base = WorldBase new
2. base advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = WorldBase.new()
val e = base.spawn()
val live_before = base.is_live(e)
base.advance()
val tick_after = base.now()
val freed = base.despawn(e)
val live_after = base.is_live(e)
expect live_before.to_equal(true)
expect tick_after.to_equal(1)
expect freed.to_equal(true)
expect live_after.to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
