# Game Engine Actor Model Specification
*Source:* `test/feature/usage/actor_model_spec.spl`
**Feature IDs:** #GE-003  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview



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

## Feature: GameMessage

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates spawn message with Vec3 | pass |
| 2 | creates set position message with Vec3 | pass |
| 3 | provides message type checks | pass |
| 4 | gets delta from update message | pass |
| 5 | converts to string | pass |

**Example:** creates spawn message with Vec3
    Given val pos = math.Vec3(1.0, 2.0, 3.0)
    Given val msg = GameMessage.Spawn(pos)
    Then  expect(msg.is_spawn() == true).to_equal(true)

**Example:** creates set position message with Vec3
    Given val pos = math.Vec3(10.0, 20.0, 30.0)
    Given val msg = GameMessage.SetPosition(pos)
    Then  expect(msg.is_set_position() == true).to_equal(true)

**Example:** provides message type checks
    Then  expect(GameMessage.Update(0.016).is_update() == true).to_equal(true)
    Then  expect(GameMessage.Despawn.is_despawn() == true).to_equal(true)
    Then  expect(GameMessage.GetPosition.is_get_position() == true).to_equal(true)
    Then  expect(GameMessage.Damage(25).is_damage() == true).to_equal(true)
    Then  expect(GameMessage.Heal(10).is_heal() == true).to_equal(true)

**Example:** gets delta from update message
    Given val msg = GameMessage.Update(0.016)
    Then  expect(msg.get_delta() == 0.016).to_equal(true)

**Example:** converts to string
    Given val msg = GameMessage.Damage(50)
    Then  expect(msg.to_string() == "Damage(50)").to_equal(true)

## Feature: EntityActor

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates with default values | pass |
| 2 | position is zero Vec3 by default | pass |
| 3 | handles SetPosition message | pass |
| 4 | handles Damage message | pass |
| 5 | handles Heal message | pass |
| 6 | dies when health reaches zero | pass |

**Example:** creates with default values
    Given val ent = EntityActor.create(1)
    Then  expect(ent.get_entity_id() == 1).to_equal(true)
    Then  expect(ent.get_health() == 100).to_equal(true)
    Then  expect(ent.get_max_health() == 100).to_equal(true)
    Then  expect(ent.is_alive() == true).to_equal(true)
    Then  expect(ent.is_full_health() == true).to_equal(true)
    Then  expect(ent.is_dead() == false).to_equal(true)

**Example:** position is zero Vec3 by default
    Given val ent = EntityActor.create(1)
    Given val pos = ent.get_position()
    Then  expect(pos.x == 0.0).to_equal(true)
    Then  expect(pos.y == 0.0).to_equal(true)
    Then  expect(pos.z == 0.0).to_equal(true)

**Example:** handles SetPosition message
    Given var ent = EntityActor.create(1)
    Given val pos = math.Vec3(10.0, 20.0, 30.0)
    Given val new_pos = ent.get_position()
    Then  expect(new_pos.x == 10.0).to_equal(true)
    Then  expect(new_pos.y == 20.0).to_equal(true)
    Then  expect(new_pos.z == 30.0).to_equal(true)

**Example:** handles Damage message
    Given var ent = EntityActor.create(1)
    Then  expect(ent.get_health() == 70).to_equal(true)

**Example:** handles Heal message
    Given var ent = EntityActor.create(1)
    Then  expect(ent.get_health() == 70).to_equal(true)

**Example:** dies when health reaches zero
    Given var ent = EntityActor.create(1)
    Then  expect(ent.get_health() == 0).to_equal(true)
    Then  expect(ent.is_alive() == false).to_equal(true)
    Then  expect(ent.is_dead() == true).to_equal(true)

## Feature: EntityManager

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | starts empty | pass |
| 2 | spawns entities with incrementing IDs | pass |
| 3 | checks entity existence | pass |
| 4 | despawns entities | pass |
| 5 | provides summary | pass |

**Example:** starts empty
    Given val mgr = EntityManager.create()
    Then  expect(mgr.is_empty() == true).to_equal(true)
    Then  expect(mgr.entity_count() == 0).to_equal(true)
    Then  expect(mgr.get_next_id() == 1).to_equal(true)

**Example:** spawns entities with incrementing IDs
    Given var mgr = EntityManager.create()
    Given val id1 = mgr.spawn_entity()
    Given val id2 = mgr.spawn_entity()
    Then  expect(id1 == 1).to_equal(true)
    Then  expect(id2 == 2).to_equal(true)
    Then  expect(mgr.entity_count() == 2).to_equal(true)
    Then  expect(mgr.has_entities() == true).to_equal(true)

**Example:** checks entity existence
    Given var mgr = EntityManager.create()
    Given val id = mgr.spawn_entity()
    Then  expect(mgr.has_entity(id) == true).to_equal(true)
    Then  expect(mgr.has_entity(999) == false).to_equal(true)

**Example:** despawns entities
    Given var mgr = EntityManager.create()
    Given val id = mgr.spawn_entity()
    Then  expect(mgr.entity_count() == 0).to_equal(true)
    Then  expect(mgr.has_entity(id) == false).to_equal(true)

**Example:** provides summary
    Given var mgr = EntityManager.create()
    Given val s = mgr.summary()
    Then  expect(s == "EntityManager: 1 entities, next_id=2").to_equal(true)


