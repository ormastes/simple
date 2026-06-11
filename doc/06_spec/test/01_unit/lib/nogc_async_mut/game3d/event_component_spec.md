# Event Component Specification

> <details>

<!-- sdn-diagram:id=event_component_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_component_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_component_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_component_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 79 | 79 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Event Component Specification

## Scenarios

### GameEventType

#### enum values

#### Custom has value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.Custom.to_i32()).to_equal(0)
```

</details>

#### EntityCreated has value 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.EntityCreated.to_i32()).to_equal(1)
```

</details>

#### EntityDestroyed has value 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.EntityDestroyed.to_i32()).to_equal(2)
```

</details>

#### CollisionEnter has value 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.CollisionEnter.to_i32()).to_equal(3)
```

</details>

#### CollisionExit has value 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.CollisionExit.to_i32()).to_equal(4)
```

</details>

#### TriggerEnter has value 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.TriggerEnter.to_i32()).to_equal(5)
```

</details>

#### TriggerExit has value 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.TriggerExit.to_i32()).to_equal(6)
```

</details>

#### InputAction has value 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.InputAction.to_i32()).to_equal(7)
```

</details>

#### SceneLoaded has value 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.SceneLoaded.to_i32()).to_equal(8)
```

</details>

#### TimerExpired has value 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameEventType.TimerExpired.to_i32()).to_equal(9)
```

</details>

### GameEvent

#### simple factory

#### creates event with given type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.simple(GameEventType.EntityCreated)
expect(ev.event_type.to_i32()).to_equal(GameEventType.EntityCreated.to_i32())
```

</details>

#### sets entity_a to -1 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.simple(GameEventType.Custom)
expect(ev.entity_a).to_equal(-1)
```

</details>

#### sets entity_b to -1 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.simple(GameEventType.Custom)
expect(ev.entity_b).to_equal(-1)
```

</details>

#### sets param_x to 0.0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.simple(GameEventType.SceneLoaded)
expect(ev.param_x).to_equal(0.0)
```

</details>

#### sets param_y to 0.0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.simple(GameEventType.SceneLoaded)
expect(ev.param_y).to_equal(0.0)
```

</details>

#### sets param_z to 0.0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.simple(GameEventType.SceneLoaded)
expect(ev.param_z).to_equal(0.0)
```

</details>

#### collision factory

#### sets event_type to CollisionEnter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.collision(1, 2, 0.0, 1.0, 0.0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.CollisionEnter.to_i32())
```

</details>

#### stores entity_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.collision(10, 20, 0.0, 0.0, 0.0)
expect(ev.entity_a).to_equal(10)
```

</details>

#### stores entity_b

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.collision(10, 20, 0.0, 0.0, 0.0)
expect(ev.entity_b).to_equal(20)
```

</details>

#### stores normal x component

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.collision(1, 2, 1.0, 0.0, 0.0)
expect(ev.param_x).to_equal(1.0)
```

</details>

#### stores normal y component

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.collision(1, 2, 0.0, 1.0, 0.0)
expect(ev.param_y).to_equal(1.0)
```

</details>

#### stores normal z component

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.collision(1, 2, 0.0, 0.0, 1.0)
expect(ev.param_z).to_equal(1.0)
```

</details>

#### trigger factory - entered

#### sets event_type to TriggerEnter when entered is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.trigger(5, 6, true)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerEnter.to_i32())
```

</details>

#### stores entity_a for trigger enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.trigger(5, 6, true)
expect(ev.entity_a).to_equal(5)
```

</details>

#### stores entity_b for trigger enter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.trigger(5, 6, true)
expect(ev.entity_b).to_equal(6)
```

</details>

#### trigger factory - exited

#### sets event_type to TriggerExit when entered is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.trigger(3, 4, false)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerExit.to_i32())
```

</details>

#### stores entity_a for trigger exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = GameEvent.trigger(3, 4, false)
expect(ev.entity_a).to_equal(3)
```

</details>

### EventQueue

#### creation

#### creates an empty queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = EventQueue.create(10)
expect(q.count()).to_equal(0)
```

</details>

#### has_events returns false when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = EventQueue.create(10)
expect(q.has_events()).to_equal(false)
```

</details>

#### push and count

#### count increases after push

1. var q = EventQueue create
2. q push
   - Expected: q.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
val ev = GameEvent.simple(GameEventType.Custom)
q.push(ev)
expect(q.count()).to_equal(1)
```

</details>

#### count increases with multiple pushes

1. var q = EventQueue create
2. q push
3. q push
   - Expected: q.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
val ev1 = GameEvent.simple(GameEventType.EntityCreated)
val ev2 = GameEvent.simple(GameEventType.EntityDestroyed)
q.push(ev1)
q.push(ev2)
expect(q.count()).to_equal(2)
```

</details>

#### has_events returns true after push

1. var q = EventQueue create
2. q push
   - Expected: q.has_events() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
val ev = GameEvent.simple(GameEventType.Custom)
q.push(ev)
expect(q.has_events()).to_equal(true)
```

</details>

#### get

#### retrieves the event at index 0

1. var q = EventQueue create
2. q push
   - Expected: got.event_type.to_i32() equals `GameEventType.EntityCreated.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
val ev = GameEvent.simple(GameEventType.EntityCreated)
q.push(ev)
val got = q.get(0)
expect(got.event_type.to_i32()).to_equal(GameEventType.EntityCreated.to_i32())
```

</details>

#### retrieves events in insertion order

1. var q = EventQueue create
2. q push
3. q push
   - Expected: first.event_type.to_i32() equals `GameEventType.EntityCreated.to_i32()`
   - Expected: second.event_type.to_i32() equals `GameEventType.EntityDestroyed.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
val ev1 = GameEvent.simple(GameEventType.EntityCreated)
val ev2 = GameEvent.simple(GameEventType.EntityDestroyed)
q.push(ev1)
q.push(ev2)
val first = q.get(0)
val second = q.get(1)
expect(first.event_type.to_i32()).to_equal(GameEventType.EntityCreated.to_i32())
expect(second.event_type.to_i32()).to_equal(GameEventType.EntityDestroyed.to_i32())
```

</details>

#### retrieves collision event fields correctly

1. var q = EventQueue create
2. q push
   - Expected: got.entity_a equals `7`
   - Expected: got.entity_b equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
val ev = GameEvent.collision(7, 8, 0.5, 0.5, 0.0)
q.push(ev)
val got = q.get(0)
expect(got.entity_a).to_equal(7)
expect(got.entity_b).to_equal(8)
```

</details>

#### clear

#### removes all events

1. var q = EventQueue create
2. q push
3. q push
4. q clear
   - Expected: q.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
q.push(GameEvent.simple(GameEventType.Custom))
q.push(GameEvent.simple(GameEventType.Custom))
q.clear()
expect(q.count()).to_equal(0)
```

</details>

#### has_events returns false after clear

1. var q = EventQueue create
2. q push
3. q clear
   - Expected: q.has_events() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
q.push(GameEvent.simple(GameEventType.Custom))
q.clear()
expect(q.has_events()).to_equal(false)
```

</details>

#### can push events again after clear

1. var q = EventQueue create
2. q push
3. q clear
4. q push
   - Expected: q.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(10)
q.push(GameEvent.simple(GameEventType.Custom))
q.clear()
q.push(GameEvent.simple(GameEventType.SceneLoaded))
expect(q.count()).to_equal(1)
```

</details>

#### overflow protection

#### does not exceed max_size on overflow

1. var q = EventQueue create
2. q push
3. q push
4. q push
5. q push
   - Expected: q.count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(3)
q.push(GameEvent.simple(GameEventType.Custom))
q.push(GameEvent.simple(GameEventType.Custom))
q.push(GameEvent.simple(GameEventType.Custom))
q.push(GameEvent.simple(GameEventType.Custom))
expect(q.count()).to_equal(3)
```

</details>

#### count stays at max_size after many pushes

1. var q = EventQueue create
2. q push
   - Expected: q.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(2)
var i = 0
while i < 10:
    q.push(GameEvent.simple(GameEventType.Custom))
    i = i + 1
expect(q.count()).to_equal(2)
```

</details>

#### existing events are preserved on overflow

1. var q = EventQueue create
2. q push
3. q push
4. q push
   - Expected: first.event_type.to_i32() equals `GameEventType.EntityCreated.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(2)
val ev1 = GameEvent.simple(GameEventType.EntityCreated)
val ev2 = GameEvent.simple(GameEventType.EntityDestroyed)
val ev3 = GameEvent.simple(GameEventType.SceneLoaded)
q.push(ev1)
q.push(ev2)
q.push(ev3)
val first = q.get(0)
expect(first.event_type.to_i32()).to_equal(GameEventType.EntityCreated.to_i32())
```

</details>

#### queue with max_size 1 holds exactly one event

1. var q = EventQueue create
2. q push
3. q push
   - Expected: q.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = EventQueue.create(1)
q.push(GameEvent.simple(GameEventType.Custom))
q.push(GameEvent.simple(GameEventType.EntityCreated))
expect(q.count()).to_equal(1)
```

</details>

### ComponentTag

#### enum values

#### Transform has value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Transform.to_i32()).to_equal(0)
```

</details>

#### Render has value 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Render.to_i32()).to_equal(1)
```

</details>

#### Physics has value 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Physics.to_i32()).to_equal(2)
```

</details>

#### Audio has value 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Audio.to_i32()).to_equal(3)
```

</details>

#### Script has value 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Script.to_i32()).to_equal(4)
```

</details>

#### Camera has value 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Camera.to_i32()).to_equal(5)
```

</details>

#### Light has value 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Light.to_i32()).to_equal(6)
```

</details>

#### Custom has value 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ComponentTag.Custom.to_i32()).to_equal(7)
```

</details>

### ComponentRegistry

#### creation

#### creates an empty registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = ComponentRegistry.create()
expect(reg.count()).to_equal(0)
```

</details>

#### add

#### count increases after add

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
expect(reg.count()).to_equal(1)
```

</details>

#### adding multiple components increases count

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
   - Expected: reg.count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
reg.add(1, ComponentTag.Render, 200)
reg.add(2, ComponentTag.Physics, 300)
expect(reg.count()).to_equal(3)
```

</details>

#### has

#### returns true after adding component

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.has(1, ComponentTag.Transform) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
expect(reg.has(1, ComponentTag.Transform)).to_equal(true)
```

</details>

#### returns false when component not added

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = ComponentRegistry.create()
expect(reg.has(1, ComponentTag.Transform)).to_equal(false)
```

</details>

#### returns false for different entity

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.has(2, ComponentTag.Transform) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
expect(reg.has(2, ComponentTag.Transform)).to_equal(false)
```

</details>

#### returns false for different tag on same entity

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.has(1, ComponentTag.Render) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
expect(reg.has(1, ComponentTag.Render)).to_equal(false)
```

</details>

#### returns true for each added tag on same entity

1. var reg = ComponentRegistry create
2. reg add
3. reg add
   - Expected: reg.has(5, ComponentTag.Transform) is true
   - Expected: reg.has(5, ComponentTag.Render) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(5, ComponentTag.Transform, 10)
reg.add(5, ComponentTag.Render, 20)
expect(reg.has(5, ComponentTag.Transform)).to_equal(true)
expect(reg.has(5, ComponentTag.Render)).to_equal(true)
```

</details>

#### get_data_id

#### returns data_id for registered component

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.get_data_id(1, ComponentTag.Transform) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 42)
expect(reg.get_data_id(1, ComponentTag.Transform)).to_equal(42)
```

</details>

#### returns -1 for unregistered component

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = ComponentRegistry.create()
expect(reg.get_data_id(1, ComponentTag.Transform)).to_equal(-1)
```

</details>

#### returns -1 for wrong entity

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.get_data_id(2, ComponentTag.Transform) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 99)
expect(reg.get_data_id(2, ComponentTag.Transform)).to_equal(-1)
```

</details>

#### returns -1 for wrong tag on same entity

1. var reg = ComponentRegistry create
2. reg add
   - Expected: reg.get_data_id(1, ComponentTag.Render) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 99)
expect(reg.get_data_id(1, ComponentTag.Render)).to_equal(-1)
```

</details>

#### returns correct data_id for each of multiple components

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
   - Expected: reg.get_data_id(3, ComponentTag.Transform) equals `10`
   - Expected: reg.get_data_id(3, ComponentTag.Render) equals `20`
   - Expected: reg.get_data_id(3, ComponentTag.Physics) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(3, ComponentTag.Transform, 10)
reg.add(3, ComponentTag.Render, 20)
reg.add(3, ComponentTag.Physics, 30)
expect(reg.get_data_id(3, ComponentTag.Transform)).to_equal(10)
expect(reg.get_data_id(3, ComponentTag.Render)).to_equal(20)
expect(reg.get_data_id(3, ComponentTag.Physics)).to_equal(30)
```

</details>

#### remove

#### component is gone after remove

1. var reg = ComponentRegistry create
2. reg add
3. reg remove
   - Expected: reg.has(1, ComponentTag.Transform) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
reg.remove(1, ComponentTag.Transform)
expect(reg.has(1, ComponentTag.Transform)).to_equal(false)
```

</details>

#### count decreases after remove

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg remove
   - Expected: reg.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
reg.add(1, ComponentTag.Render, 200)
reg.remove(1, ComponentTag.Transform)
expect(reg.count()).to_equal(1)
```

</details>

#### other components remain after targeted remove

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg remove
   - Expected: reg.has(1, ComponentTag.Render) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
reg.add(1, ComponentTag.Render, 200)
reg.remove(1, ComponentTag.Transform)
expect(reg.has(1, ComponentTag.Render)).to_equal(true)
```

</details>

#### get_data_id returns -1 after remove

1. var reg = ComponentRegistry create
2. reg add
3. reg remove
   - Expected: reg.get_data_id(1, ComponentTag.Transform) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 55)
reg.remove(1, ComponentTag.Transform)
expect(reg.get_data_id(1, ComponentTag.Transform)).to_equal(-1)
```

</details>

#### removing non-existent component leaves count unchanged

1. var reg = ComponentRegistry create
2. reg add
3. reg remove
   - Expected: reg.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Render, 10)
reg.remove(1, ComponentTag.Transform)
expect(reg.count()).to_equal(1)
```

</details>

#### components of other entities are unaffected by remove

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg remove
   - Expected: reg.has(2, ComponentTag.Transform) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 100)
reg.add(2, ComponentTag.Transform, 200)
reg.remove(1, ComponentTag.Transform)
expect(reg.has(2, ComponentTag.Transform)).to_equal(true)
```

</details>

#### count_by_tag

#### returns 0 for empty registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = ComponentRegistry.create()
expect(reg.count_by_tag(ComponentTag.Transform)).to_equal(0)
```

</details>

#### counts components of a specific tag

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
   - Expected: reg.count_by_tag(ComponentTag.Transform) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 10)
reg.add(2, ComponentTag.Transform, 20)
reg.add(3, ComponentTag.Render, 30)
expect(reg.count_by_tag(ComponentTag.Transform)).to_equal(2)
```

</details>

#### does not count other tags

1. var reg = ComponentRegistry create
2. reg add
3. reg add
   - Expected: reg.count_by_tag(ComponentTag.Transform) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Render, 10)
reg.add(2, ComponentTag.Physics, 20)
expect(reg.count_by_tag(ComponentTag.Transform)).to_equal(0)
```

</details>

#### counts each tag independently

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
5. reg add
   - Expected: reg.count_by_tag(ComponentTag.Transform) equals `3`
   - Expected: reg.count_by_tag(ComponentTag.Render) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 1)
reg.add(2, ComponentTag.Transform, 2)
reg.add(3, ComponentTag.Transform, 3)
reg.add(1, ComponentTag.Render, 4)
expect(reg.count_by_tag(ComponentTag.Transform)).to_equal(3)
expect(reg.count_by_tag(ComponentTag.Render)).to_equal(1)
```

</details>

#### decreases after remove

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg remove
   - Expected: reg.count_by_tag(ComponentTag.Audio) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Audio, 10)
reg.add(2, ComponentTag.Audio, 20)
reg.remove(1, ComponentTag.Audio)
expect(reg.count_by_tag(ComponentTag.Audio)).to_equal(1)
```

</details>

#### remove_all

#### removes all components for an entity

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
5. reg remove all
   - Expected: reg.has(1, ComponentTag.Transform) is false
   - Expected: reg.has(1, ComponentTag.Render) is false
   - Expected: reg.has(1, ComponentTag.Physics) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 10)
reg.add(1, ComponentTag.Render, 20)
reg.add(1, ComponentTag.Physics, 30)
reg.remove_all(1)
expect(reg.has(1, ComponentTag.Transform)).to_equal(false)
expect(reg.has(1, ComponentTag.Render)).to_equal(false)
expect(reg.has(1, ComponentTag.Physics)).to_equal(false)
```

</details>

#### count drops to zero after remove_all for sole entity

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg remove all
   - Expected: reg.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 10)
reg.add(1, ComponentTag.Camera, 20)
reg.remove_all(1)
expect(reg.count()).to_equal(0)
```

</details>

#### other entities are unaffected by remove_all

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
5. reg remove all
   - Expected: reg.has(2, ComponentTag.Transform) is true
   - Expected: reg.has(2, ComponentTag.Render) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 10)
reg.add(2, ComponentTag.Transform, 20)
reg.add(2, ComponentTag.Render, 30)
reg.remove_all(1)
expect(reg.has(2, ComponentTag.Transform)).to_equal(true)
expect(reg.has(2, ComponentTag.Render)).to_equal(true)
```

</details>

#### count reflects only remaining components after remove_all

1. var reg = ComponentRegistry create
2. reg add
3. reg add
4. reg add
5. reg remove all
   - Expected: reg.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Script, 1)
reg.add(1, ComponentTag.Light, 2)
reg.add(2, ComponentTag.Camera, 3)
reg.remove_all(1)
expect(reg.count()).to_equal(1)
```

</details>

#### remove_all on non-existent entity leaves registry unchanged

1. var reg = ComponentRegistry create
2. reg add
3. reg remove all
   - Expected: reg.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry.create()
reg.add(1, ComponentTag.Transform, 10)
reg.remove_all(99)
expect(reg.count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/event_component_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GameEventType
- GameEvent
- EventQueue
- ComponentTag
- ComponentRegistry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 79 |
| Active scenarios | 79 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
