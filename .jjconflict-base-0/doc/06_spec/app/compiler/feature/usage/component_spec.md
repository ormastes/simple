# Game Engine Component Specification

Component system with ComponentType enum, Component trait, and ComponentManager.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GE-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/component_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview
Component system with ComponentType enum, Component trait, and ComponentManager.

## Key Concepts
| Concept | Description |
|---------|-------------|
| ComponentType | Enum of standard component categories |
| Component | Trait for component lifecycle |
| ComponentManager | Manages components on an entity |

## Behavior
- ComponentType provides is_* helpers and descriptions
- ComponentManager supports add, remove, query by type
- Trait-only design (no FFI adapters)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/component/result.json` |

## Scenarios

- converts to string
- provides descriptions
- checks type categories
- checks visual and simulation
- starts empty
- provides summary
