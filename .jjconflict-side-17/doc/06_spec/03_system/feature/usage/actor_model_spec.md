# Game Engine Actor Model Specification

> Actor model for game entities with Vec3 positions and message-passing.

<!-- sdn-diagram:id=actor_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_model_spec -> math
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=actor_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Engine Actor Model Specification

Actor model for game entities with Vec3 positions and message-passing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GE-003 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/actor_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Actor model for game entities with Vec3 positions and message-passing.

## Key Concepts
| Concept | Description |
|---------|-------------|
| GameMessage | Enum of standard game messages |
| EntityActor | Actor wrapper for game entities |
| EntityManager | Manages collections of entity actors |

## Behavior
- GameMessage uses math.Vec3 for positions
- EntityActor tracks position, health, alive state
- EntityManager provides spawn, despawn, message dispatch

## Scenarios

### GameMessage

#### creates spawn message with Vec3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = math.Vec3(1.0, 2.0, 3.0)
val msg = GameMessage.Spawn(pos)
expect(msg.is_spawn() == true).to_equal(true)
```

</details>

#### creates set position message with Vec3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = math.Vec3(10.0, 20.0, 30.0)
val msg = GameMessage.SetPosition(pos)
expect(msg.is_set_position() == true).to_equal(true)
```

</details>

#### provides message type checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GameMessage.Update(0.016).is_update() == true).to_equal(true)
expect(GameMessage.Despawn.is_despawn() == true).to_equal(true)
expect(GameMessage.GetPosition.is_get_position() == true).to_equal(true)
expect(GameMessage.Damage(25).is_damage() == true).to_equal(true)
expect(GameMessage.Heal(10).is_heal() == true).to_equal(true)
```

</details>

#### gets delta from update message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = GameMessage.Update(0.016)
expect(msg.get_delta() == 0.016).to_equal(true)
```

</details>

#### converts to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = GameMessage.Damage(50)
expect(msg.to_string() == "Damage(50)").to_equal(true)
```

</details>

### EntityActor

#### creates with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ent = EntityActor.create(1)
expect(ent.get_entity_id() == 1).to_equal(true)
expect(ent.get_health() == 100).to_equal(true)
expect(ent.get_max_health() == 100).to_equal(true)
expect(ent.is_alive() == true).to_equal(true)
expect(ent.is_full_health() == true).to_equal(true)
expect(ent.is_dead() == false).to_equal(true)
```

</details>

#### position is zero Vec3 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ent = EntityActor.create(1)
val pos = ent.get_position()
expect(pos.x == 0.0).to_equal(true)
expect(pos.y == 0.0).to_equal(true)
expect(pos.z == 0.0).to_equal(true)
```

</details>

#### handles SetPosition message

1. var ent = EntityActor create
2. ent handle message
   - Expected: new_pos.x == 10.0 is true
   - Expected: new_pos.y == 20.0 is true
   - Expected: new_pos.z == 30.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ent = EntityActor.create(1)
val pos = math.Vec3(10.0, 20.0, 30.0)
ent.handle_message(GameMessage.SetPosition(pos))
val new_pos = ent.get_position()
expect(new_pos.x == 10.0).to_equal(true)
expect(new_pos.y == 20.0).to_equal(true)
expect(new_pos.z == 30.0).to_equal(true)
```

</details>

#### handles Damage message

1. var ent = EntityActor create
2. ent handle message
   - Expected: ent.get_health() == 70 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ent = EntityActor.create(1)
ent.handle_message(GameMessage.Damage(30))
expect(ent.get_health() == 70).to_equal(true)
```

</details>

#### handles Heal message

1. var ent = EntityActor create
2. ent handle message
3. ent handle message
   - Expected: ent.get_health() == 70 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ent = EntityActor.create(1)
ent.handle_message(GameMessage.Damage(50))
ent.handle_message(GameMessage.Heal(20))
expect(ent.get_health() == 70).to_equal(true)
```

</details>

#### dies when health reaches zero

1. var ent = EntityActor create
2. ent handle message
   - Expected: ent.get_health() == 0 is true
   - Expected: ent.is_alive() == false is true
   - Expected: ent.is_dead() == true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ent = EntityActor.create(1)
ent.handle_message(GameMessage.Damage(100))
expect(ent.get_health() == 0).to_equal(true)
expect(ent.is_alive() == false).to_equal(true)
expect(ent.is_dead() == true).to_equal(true)
```

</details>

### EntityManager

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = EntityManager.create()
expect(mgr.is_empty() == true).to_equal(true)
expect(mgr.entity_count() == 0).to_equal(true)
expect(mgr.get_next_id() == 1).to_equal(true)
```

</details>

#### spawns entities with incrementing IDs

1. var mgr = EntityManager create
   - Expected: id1 == 1 is true
   - Expected: id2 == 2 is true
   - Expected: mgr.entity_count() == 2 is true
   - Expected: mgr.has_entities() == true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = EntityManager.create()
val id1 = mgr.spawn_entity()
val id2 = mgr.spawn_entity()
expect(id1 == 1).to_equal(true)
expect(id2 == 2).to_equal(true)
expect(mgr.entity_count() == 2).to_equal(true)
expect(mgr.has_entities() == true).to_equal(true)
```

</details>

#### checks entity existence

1. var mgr = EntityManager create
   - Expected: mgr.has_entity(id) == true is true
   - Expected: mgr.has_entity(999) == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = EntityManager.create()
val id = mgr.spawn_entity()
expect(mgr.has_entity(id) == true).to_equal(true)
expect(mgr.has_entity(999) == false).to_equal(true)
```

</details>

#### despawns entities

1. var mgr = EntityManager create
2. mgr despawn entity
   - Expected: mgr.entity_count() == 0 is true
   - Expected: mgr.has_entity(id) == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = EntityManager.create()
val id = mgr.spawn_entity()
mgr.despawn_entity(id)
expect(mgr.entity_count() == 0).to_equal(true)
expect(mgr.has_entity(id) == false).to_equal(true)
```

</details>

#### provides summary

1. var mgr = EntityManager create
2. mgr spawn entity
   - Expected: s == "EntityManager: 1 entities, next_id=2" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = EntityManager.create()
mgr.spawn_entity()
val s = mgr.summary()
expect(s == "EntityManager: 1 entities, next_id=2").to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
