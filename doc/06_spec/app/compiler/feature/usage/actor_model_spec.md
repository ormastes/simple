# Game Engine Actor Model Specification

Actor model for game entities with Vec3 positions and message-passing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GE-003 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/actor_model_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/actor_model/result.json` |

## Scenarios

- creates spawn message with Vec3
- creates set position message with Vec3
- provides message type checks
- gets delta from update message
- converts to string
- creates with default values
- position is zero Vec3 by default
- handles SetPosition message
- handles Damage message
- handles Heal message
- dies when health reaches zero
- starts empty
- spawns entities with incrementing IDs
- checks entity existence
- despawns entities
- provides summary
