# Game Engine Component Specification
*Source:* `test/feature/usage/component_spec.spl`
**Feature IDs:** #GE-001  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview



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

## Feature: ComponentType

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | converts to string | pass |
| 2 | provides descriptions | pass |
| 3 | checks type categories | pass |
| 4 | checks visual and simulation | pass |

**Example:** converts to string
    Then  expect ComponentType.Transform.to_string() == "Transform"
    Then  expect ComponentType.Render.to_string() == "Render"
    Then  expect ComponentType.Physics.to_string() == "Physics"
    Then  expect ComponentType.Audio.to_string() == "Audio"
    Then  expect ComponentType.Script.to_string() == "Script"
    Then  expect ComponentType.Custom.to_string() == "Custom"

**Example:** provides descriptions
    Given val desc = ComponentType.Physics.description()
    Then  expect desc == "Physics simulation and collision"

**Example:** checks type categories
    Then  expect ComponentType.Transform.is_transform() == true
    Then  expect ComponentType.Render.is_render() == true
    Then  expect ComponentType.Physics.is_physics() == true

**Example:** checks visual and simulation
    Then  expect ComponentType.Render.is_visual() == true
    Then  expect ComponentType.Physics.is_simulation() == true
    Then  expect ComponentType.Transform.is_simulation() == true
    Then  expect ComponentType.Render.is_output() == true
    Then  expect ComponentType.Audio.is_output() == true

## Feature: ComponentManager

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | starts empty | pass |
| 2 | provides summary | pass |

**Example:** starts empty
    Given val mgr = ComponentManager.create()
    Then  expect mgr.is_empty() == true
    Then  expect mgr.count() == 0
    Then  expect mgr.has_components() == false

**Example:** provides summary
    Given val mgr = ComponentManager.create()
    Given val s = mgr.summary()
    Then  expect s == "ComponentManager: 0 components, 0 enabled, 0 initialized"


