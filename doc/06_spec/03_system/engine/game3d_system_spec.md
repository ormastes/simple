# Game3D System Integration Tests

> End-to-end system tests verifying the game3d library components work together: math types, event queue, component registry, game loop callbacks, and key codes. These tests verify the full integration path, not isolated units.

<!-- sdn-diagram:id=game3d_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game3d_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game3d_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game3d_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game3D System Integration Tests

End-to-end system tests verifying the game3d library components work together: math types, event queue, component registry, game loop callbacks, and key codes. These tests verify the full integration path, not isolated units.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GAME3D-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/engine/game3d_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end system tests verifying the game3d library components work together:
math types, event queue, component registry, game loop callbacks, and key codes.
These tests verify the full integration path, not isolated units.

## Scenarios

### Component Registry - Entity Lifecycle

#### adds Transform, Render, and Physics components to entity 1

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
   - Expected: registry.has(1, ComponentTag.Transform) is true
   - Expected: registry.has(1, ComponentTag.Render) is true
   - Expected: registry.has(1, ComponentTag.Physics) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Transform, 100)
registry.add(1, ComponentTag.Render, 101)
registry.add(1, ComponentTag.Physics, 102)

expect(registry.has(1, ComponentTag.Transform)).to_equal(true)
expect(registry.has(1, ComponentTag.Render)).to_equal(true)
expect(registry.has(1, ComponentTag.Physics)).to_equal(true)
```

</details>

#### returns correct data_ids for added components

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
   - Expected: registry.get_data_id(1, ComponentTag.Transform) equals `100`
   - Expected: registry.get_data_id(1, ComponentTag.Render) equals `101`
   - Expected: registry.get_data_id(1, ComponentTag.Physics) equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Transform, 100)
registry.add(1, ComponentTag.Render, 101)
registry.add(1, ComponentTag.Physics, 102)

expect(registry.get_data_id(1, ComponentTag.Transform)).to_equal(100)
expect(registry.get_data_id(1, ComponentTag.Render)).to_equal(101)
expect(registry.get_data_id(1, ComponentTag.Physics)).to_equal(102)
```

</details>

#### removes Physics component while keeping Transform and Render

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
5. registry remove
   - Expected: registry.has(1, ComponentTag.Physics) is false
   - Expected: registry.has(1, ComponentTag.Transform) is true
   - Expected: registry.has(1, ComponentTag.Render) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Transform, 100)
registry.add(1, ComponentTag.Render, 101)
registry.add(1, ComponentTag.Physics, 102)

registry.remove(1, ComponentTag.Physics)

expect(registry.has(1, ComponentTag.Physics)).to_equal(false)
expect(registry.has(1, ComponentTag.Transform)).to_equal(true)
expect(registry.has(1, ComponentTag.Render)).to_equal(true)
```

</details>

#### remove_all clears all components for entity 1

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
5. registry add
6. registry remove all
   - Expected: registry.has(1, ComponentTag.Transform) is false
   - Expected: registry.has(1, ComponentTag.Render) is false
   - Expected: registry.has(1, ComponentTag.Physics) is false
   - Expected: registry.has(2, ComponentTag.Transform) is true
   - Expected: registry.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Transform, 100)
registry.add(1, ComponentTag.Render, 101)
registry.add(1, ComponentTag.Physics, 102)
registry.add(2, ComponentTag.Transform, 200)

registry.remove_all(1)

expect(registry.has(1, ComponentTag.Transform)).to_equal(false)
expect(registry.has(1, ComponentTag.Render)).to_equal(false)
expect(registry.has(1, ComponentTag.Physics)).to_equal(false)
# Entity 2 still intact
expect(registry.has(2, ComponentTag.Transform)).to_equal(true)
expect(registry.count()).to_equal(1)
```

</details>

#### returns -1 for data_id of missing component

1. var registry = ComponentRegistry create
   - Expected: registry.get_data_id(99, ComponentTag.Physics) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
expect(registry.get_data_id(99, ComponentTag.Physics)).to_equal(-1)
```

</details>

### Event Queue - Collision and Trigger Flow

#### accepts collision event and trigger enter event

1. var queue = EventQueue create
2. queue push
3. queue push
   - Expected: queue.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(64)
val col = GameEvent.collision(10, 20, 0.0, 1.0, 0.0)
val trig = GameEvent.trigger(5, 6, true)
queue.push(col)
queue.push(trig)

expect(queue.count()).to_equal(2)
```

</details>

#### reads back correct entity IDs from collision event

1. var queue = EventQueue create
2. queue push
   - Expected: ev.entity_a equals `10`
   - Expected: ev.entity_b equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(64)
val col = GameEvent.collision(10, 20, 0.0, 1.0, 0.0)
queue.push(col)

val ev = queue.get(0)
expect(ev.entity_a).to_equal(10)
expect(ev.entity_b).to_equal(20)
```

</details>

#### reads back correct normal from collision event

1. var queue = EventQueue create
2. queue push
   - Expected: ev.param_x equals `0.0`
   - Expected: ev.param_y equals `1.0`
   - Expected: ev.param_z equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(64)
val col = GameEvent.collision(10, 20, 0.0, 1.0, 0.0)
queue.push(col)

val ev = queue.get(0)
expect(ev.param_x).to_equal(0.0)
expect(ev.param_y).to_equal(1.0)
expect(ev.param_z).to_equal(0.0)
```

</details>

#### reads back TriggerEnter event type

1. var queue = EventQueue create
2. queue push
   - Expected: ev.event_type.to_i32() equals `GameEventType.TriggerEnter.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(64)
val trig = GameEvent.trigger(5, 6, true)
queue.push(trig)

val ev = queue.get(0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerEnter.to_i32())
```

</details>

#### has_events returns true when queue has events

1. var queue = EventQueue create
2. queue push
   - Expected: queue.has_events() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(64)
queue.push(GameEvent.simple(GameEventType.EntityCreated))
expect(queue.has_events()).to_equal(true)
```

</details>

#### clear empties the queue

1. var queue = EventQueue create
2. queue push
3. queue push
4. queue clear
   - Expected: queue.count() equals `0`
   - Expected: queue.has_events() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(64)
queue.push(GameEvent.collision(1, 2, 1.0, 0.0, 0.0))
queue.push(GameEvent.collision(3, 4, 0.0, 0.0, 1.0))
queue.clear()

expect(queue.count()).to_equal(0)
expect(queue.has_events()).to_equal(false)
```

</details>

#### does not exceed max_size

1. var queue = EventQueue create
2. queue push
3. queue push
4. queue push
   - Expected: queue.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = EventQueue.create(2)
queue.push(GameEvent.simple(GameEventType.Custom))
queue.push(GameEvent.simple(GameEventType.Custom))
queue.push(GameEvent.simple(GameEventType.Custom))

expect(queue.count()).to_equal(2)
```

</details>

### Math - Vec3 operations

#### adds two Vec3 values correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 2.0, 3.0)
val b = Vec3(4.0, 5.0, 6.0)
val c = a.add(b)
expect(c.x).to_equal(5.0)
expect(c.y).to_equal(7.0)
expect(c.z).to_equal(9.0)
```

</details>

#### dot product of orthogonal vectors is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val up = Vec3.up()
val right = Vec3.right()
val d = up.dot(right)
expect(d).to_equal(0.0)
```

</details>

#### cross product of forward and right gives down

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = Vec3.forward()
val right = Vec3.right()
val cross = fwd.cross(right)
# forward(0,0,1) x right(1,0,0) = (0*0-1*0, 1*1-0*0, 0*0-0*1) = (0,1,0) negate = down
# Actually: (fy*rz - fz*ry, fz*rx - fx*rz, fx*ry - fy*rx)
# = (0*0 - 1*0, 1*1 - 0*0, 0*0 - 0*1) = (0, 1, 0) = up
expect(cross.y).to_equal(1.0)
```

</details>

#### normalizes a Vec3 to unit length

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(3.0, 0.0, 4.0)
val n = v.normalize()
val len = n.length()
# length_squared should be ~1.0; check magnitude is 1.0
val len_sq = n.x * n.x + n.y * n.y + n.z * n.z
expect(len_sq).to_be_greater_than(0.99)
expect(len_sq).to_be_less_than(1.01)
```

</details>

#### lerp at t=0 returns first vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(0.0, 0.0, 0.0)
val b = Vec3(10.0, 10.0, 10.0)
val result = a.lerp(b, 0.0)
expect(result.x).to_equal(0.0)
expect(result.y).to_equal(0.0)
expect(result.z).to_equal(0.0)
```

</details>

#### lerp at t=1 returns second vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(0.0, 0.0, 0.0)
val b = Vec3(10.0, 10.0, 10.0)
val result = a.lerp(b, 1.0)
expect(result.x).to_equal(10.0)
expect(result.y).to_equal(10.0)
expect(result.z).to_equal(10.0)
```

</details>

### Math - Transform point transformation

#### identity transform leaves point unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val p = Vec3(5.0, 3.0, 2.0)
val result = t.transform_point(p)
expect(result.x).to_equal(5.0)
expect(result.y).to_equal(3.0)
expect(result.z).to_equal(2.0)
```

</details>

#### translation-only transform shifts point by position

1. position: Vec3
2. rotation: Quat identity
3. scale : Vec3 one
   - Expected: result.x equals `1.0`
   - Expected: result.y equals `2.0`
   - Expected: result.z equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform(
    position: Vec3(1.0, 2.0, 3.0),
    rotation: Quat.identity(),
    scale_: Vec3.one()
)
val p = Vec3(0.0, 0.0, 0.0)
val result = t.transform_point(p)
expect(result.x).to_equal(1.0)
expect(result.y).to_equal(2.0)
expect(result.z).to_equal(3.0)
```

</details>

#### 90-degree Y-axis rotation transforms X-axis toward -Z

1. position: Vec3 zero
2. scale : Vec3 one


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val half_pi: f32 = 1.5707963
val rot = Quat.from_axis_angle(Vec3.up(), half_pi)
val t = Transform(
    position: Vec3.zero(),
    rotation: rot,
    scale_: Vec3.one()
)
val p = Vec3(1.0, 0.0, 0.0)
val result = t.transform_point(p)
# 90-degree Y rotation: X -> -Z
expect(result.x).to_be_greater_than(-0.01)
expect(result.x).to_be_less_than(0.01)
expect(result.y).to_be_greater_than(-0.01)
expect(result.y).to_be_less_than(0.01)
expect(result.z).to_be_less_than(-0.99)
```

</details>

#### translation then rotation places point correctly

1. position: Vec3
2. rotation: Quat identity
3. scale : Vec3 one
   - Expected: result.x equals `11.0`
   - Expected: result.y equals `0.0`
   - Expected: result.z equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform(
    position: Vec3(10.0, 0.0, 0.0),
    rotation: Quat.identity(),
    scale_: Vec3.one()
)
val p = Vec3(1.0, 0.0, 0.0)
val result = t.transform_point(p)
expect(result.x).to_equal(11.0)
expect(result.y).to_equal(0.0)
expect(result.z).to_equal(0.0)
```

</details>

### Math - AABB intersection

#### overlapping AABBs intersect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(2.0, 2.0, 2.0))
val b = AABB(min: Vec3(1.0, 1.0, 1.0), max: Vec3(3.0, 3.0, 3.0))
expect(a.intersects(b)).to_equal(true)
```

</details>

#### non-overlapping AABBs do not intersect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(1.0, 1.0, 1.0))
val b = AABB(min: Vec3(2.0, 2.0, 2.0), max: Vec3(3.0, 3.0, 3.0))
expect(a.intersects(b)).to_equal(false)
```

</details>

#### contains_point returns true for interior point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(4.0, 4.0, 4.0))
expect(box.contains_point(Vec3(2.0, 2.0, 2.0))).to_equal(true)
```

</details>

#### contains_point returns false for exterior point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(4.0, 4.0, 4.0))
expect(box.contains_point(Vec3(5.0, 5.0, 5.0))).to_equal(false)
```

</details>

#### from_center_extents creates correct bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB.from_center_extents(Vec3(0.0, 0.0, 0.0), Vec3(1.0, 1.0, 1.0))
expect(box.min.x).to_equal(-1.0)
expect(box.max.x).to_equal(1.0)
```

</details>

### Math - Ray point_at

#### point_at t=0 is origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3(1.0, 2.0, 3.0), direction: Vec3(0.0, 0.0, 1.0))
val p = r.point_at(0.0)
expect(p.x).to_equal(1.0)
expect(p.y).to_equal(2.0)
expect(p.z).to_equal(3.0)
```

</details>

#### point_at t=5 advances along direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3(0.0, 0.0, 0.0), direction: Vec3(1.0, 0.0, 0.0))
val p = r.point_at(5.0)
expect(p.x).to_equal(5.0)
expect(p.y).to_equal(0.0)
expect(p.z).to_equal(0.0)
```

</details>

#### ray normalizes its direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3.zero(), direction: Vec3(3.0, 0.0, 4.0))
val len_sq = r.direction.x * r.direction.x + r.direction.y * r.direction.y + r.direction.z * r.direction.z
expect(len_sq).to_be_greater_than(0.99)
expect(len_sq).to_be_less_than(1.01)
```

</details>

### Game Loop - Callback Registration and Invocation

#### game_init calls registered init callback

1. test on init
   - Expected: _init_ran is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_init_ran = false
test_on_init()
expect(_init_ran).to_equal(true)
```

</details>

#### on_collision pushes events to the shared queue

1. q clear
2. q push
3. q push
   - Expected: q.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = EventQueue.create(64)
q.clear()
q.push(GameEvent.collision(10, 20, 0.0, 1.0, 0.0))
q.push(GameEvent.collision(30, 40, 1.0, 0.0, 0.0))
expect(q.count()).to_equal(2)
```

</details>

#### game_update clears the event queue then calls update callback

1. q clear
2. q push
   - Expected: q.count() equals `1`
3. q clear
4. test on update
   - Expected: _update_ran is true
   - Expected: q.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_update_ran = false
_last_dt = 0.0

val q = EventQueue.create(64)
q.clear()
q.push(GameEvent.collision(1, 2, 0.0, 1.0, 0.0))
expect(q.count()).to_equal(1)

q.clear()
test_on_update(0.016)

expect(_update_ran).to_equal(true)
expect(q.count()).to_equal(0)
```

</details>

#### game_update passes correct delta time to callback

1. test on update


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_last_dt = 0.0
test_on_update(0.033)
expect(_last_dt).to_be_greater_than(0.032)
expect(_last_dt).to_be_less_than(0.034)
```

</details>

#### game_shutdown calls registered shutdown callback

1. test on shutdown
   - Expected: _shutdown_ran is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_shutdown_ran = false
test_on_shutdown()
expect(_shutdown_ran).to_equal(true)
```

</details>

#### on_trigger pushes TriggerEnter event to shared queue

1. q clear
2. q push
   - Expected: q.count() equals `1`
   - Expected: ev.event_type.to_i32() equals `GameEventType.TriggerEnter.to_i32()`
   - Expected: ev.entity_a equals `5`
   - Expected: ev.entity_b equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = EventQueue.create(64)
q.clear()
q.push(GameEvent.trigger(5, 6, true))
expect(q.count()).to_equal(1)
val ev = q.get(0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerEnter.to_i32())
expect(ev.entity_a).to_equal(5)
expect(ev.entity_b).to_equal(6)
```

</details>

#### on_trigger with entered=0 pushes TriggerExit event

1. q clear
2. q push
   - Expected: q.count() equals `1`
   - Expected: ev.event_type.to_i32() equals `GameEventType.TriggerExit.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = EventQueue.create(64)
q.clear()
q.push(GameEvent.trigger(7, 8, false))
expect(q.count()).to_equal(1)
val ev = q.get(0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerExit.to_i32())
```

</details>

### Component and Event Integration

#### both colliding entities have Physics components

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
5. var queue = EventQueue create
6. queue push
   - Expected: registry.has(ea, ComponentTag.Physics) is true
   - Expected: registry.has(eb, ComponentTag.Physics) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Physics, 10)
registry.add(2, ComponentTag.Physics, 20)
registry.add(3, ComponentTag.Physics, 30)

var queue = EventQueue.create(64)
val col = GameEvent.collision(1, 2, 0.0, 1.0, 0.0)
queue.push(col)

val ev = queue.get(0)
val ea = ev.entity_a
val eb = ev.entity_b

expect(registry.has(ea, ComponentTag.Physics)).to_equal(true)
expect(registry.has(eb, ComponentTag.Physics)).to_equal(true)
```

</details>

#### removing all components from entity 2 leaves entity 1 intact

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
5. registry add
6. registry add
7. registry remove all
   - Expected: registry.has(2, ComponentTag.Transform) is false
   - Expected: registry.has(2, ComponentTag.Physics) is false
   - Expected: registry.has(2, ComponentTag.Render) is false
   - Expected: registry.has(1, ComponentTag.Transform) is true
   - Expected: registry.has(1, ComponentTag.Physics) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Transform, 10)
registry.add(1, ComponentTag.Physics, 11)
registry.add(2, ComponentTag.Transform, 20)
registry.add(2, ComponentTag.Physics, 21)
registry.add(2, ComponentTag.Render, 22)

registry.remove_all(2)

expect(registry.has(2, ComponentTag.Transform)).to_equal(false)
expect(registry.has(2, ComponentTag.Physics)).to_equal(false)
expect(registry.has(2, ComponentTag.Render)).to_equal(false)
expect(registry.has(1, ComponentTag.Transform)).to_equal(true)
expect(registry.has(1, ComponentTag.Physics)).to_equal(true)
```

</details>

#### count_by_tag counts only components of matching type

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
   - Expected: registry.count_by_tag(ComponentTag.Physics) equals `2`
   - Expected: registry.count_by_tag(ComponentTag.Transform) equals `1`
   - Expected: registry.count_by_tag(ComponentTag.Render) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Physics, 10)
registry.add(2, ComponentTag.Physics, 20)
registry.add(3, ComponentTag.Transform, 30)

expect(registry.count_by_tag(ComponentTag.Physics)).to_equal(2)
expect(registry.count_by_tag(ComponentTag.Transform)).to_equal(1)
expect(registry.count_by_tag(ComponentTag.Render)).to_equal(0)
```

</details>

#### multi-entity collision event triggers lookup for all entities

1. var registry = ComponentRegistry create
2. registry add
3. registry add
4. registry add
5. var queue = EventQueue create
6. queue push
7. queue push
   - Expected: registry.has(ev1.entity_a, ComponentTag.Physics) is true
   - Expected: registry.has(ev1.entity_b, ComponentTag.Physics) is true
   - Expected: registry.has(ev2.entity_b, ComponentTag.Render) is true
   - Expected: registry.has(ev2.entity_b, ComponentTag.Physics) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ComponentRegistry.create()
registry.add(1, ComponentTag.Physics, 100)
registry.add(2, ComponentTag.Physics, 200)
registry.add(3, ComponentTag.Render, 300)

var queue = EventQueue.create(64)
queue.push(GameEvent.collision(1, 2, 0.0, 1.0, 0.0))
queue.push(GameEvent.collision(2, 3, 1.0, 0.0, 0.0))

val ev1 = queue.get(0)
val ev2 = queue.get(1)

# Both entities in first collision have Physics
expect(registry.has(ev1.entity_a, ComponentTag.Physics)).to_equal(true)
expect(registry.has(ev1.entity_b, ComponentTag.Physics)).to_equal(true)

# Entity 3 in second collision has Render, not Physics
expect(registry.has(ev2.entity_b, ComponentTag.Render)).to_equal(true)
expect(registry.has(ev2.entity_b, ComponentTag.Physics)).to_equal(false)
```

</details>

### KeyCode - WASD letters and arrow classification

#### W is a letter key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.W.is_letter()).to_equal(true)
```

</details>

#### A is a letter key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.A.is_letter()).to_equal(true)
```

</details>

#### S is a letter key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.S.is_letter()).to_equal(true)
```

</details>

#### D is a letter key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.D.is_letter()).to_equal(true)
```

</details>

#### Up arrow is an arrow key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Up.is_arrow()).to_equal(true)
```

</details>

#### Down arrow is an arrow key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Down.is_arrow()).to_equal(true)
```

</details>

#### Left arrow is an arrow key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Left.is_arrow()).to_equal(true)
```

</details>

#### Right arrow is an arrow key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Right.is_arrow()).to_equal(true)
```

</details>

#### arrow keys are not letter keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Up.is_letter()).to_equal(false)
expect(KeyCode.Down.is_letter()).to_equal(false)
expect(KeyCode.Left.is_letter()).to_equal(false)
expect(KeyCode.Right.is_letter()).to_equal(false)
```

</details>

#### letter keys are not arrow keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.W.is_arrow()).to_equal(false)
expect(KeyCode.A.is_arrow()).to_equal(false)
```

</details>

#### letter keys are not function keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.W.is_function_key()).to_equal(false)
expect(KeyCode.S.is_function_key()).to_equal(false)
```

</details>

#### F1 through F4 are function keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.F1.is_function_key()).to_equal(true)
expect(KeyCode.F2.is_function_key()).to_equal(true)
expect(KeyCode.F3.is_function_key()).to_equal(true)
expect(KeyCode.F4.is_function_key()).to_equal(true)
```

</details>

#### digit keys are digits but not letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Num0.is_digit()).to_equal(true)
expect(KeyCode.Num9.is_digit()).to_equal(true)
expect(KeyCode.Num0.is_letter()).to_equal(false)
```

</details>

#### modifier keys are recognized

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.LeftShift.is_modifier()).to_equal(true)
expect(KeyCode.LeftCtrl.is_modifier()).to_equal(true)
expect(KeyCode.RightAlt.is_modifier()).to_equal(true)
```

</details>

#### letter keys are not modifier keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.W.is_modifier()).to_equal(false)
```

</details>

#### to_i32 returns correct raw value for W

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.W.to_i32()).to_equal(87)
```

</details>

#### to_i32 returns correct raw value for Space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(KeyCode.Space.to_i32()).to_equal(32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
