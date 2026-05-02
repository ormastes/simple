# Game Engine Actor Model Specification

**Feature ID:** #GE-003 | **Category:** Stdlib | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/actor_model_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### GameMessage

- ✅ creates spawn message with Vec3
- ✅ creates set position message with Vec3
- ✅ provides message type checks
- ✅ gets delta from update message
- ✅ converts to string
### EntityActor

- ✅ creates with default values
- ✅ position is zero Vec3 by default
- ✅ handles SetPosition message
- ✅ handles Damage message
- ✅ handles Heal message
- ✅ dies when health reaches zero
### EntityManager

- ✅ starts empty
- ✅ spawns entities with incrementing IDs
- ✅ checks entity existence
- ✅ despawns entities
- ✅ provides summary

