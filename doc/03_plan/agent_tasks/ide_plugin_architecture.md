<!-- codex-design -->
# Agent Tasks: IDE Plugin Architecture

## Slice 1: Manifest Registry

- Add common manifest and contribution structs.
- Add built-in Office plugin manifests.
- Add registry validation and contribution indexes.
- Route IDE feature report through the registry.

## Slice 2: Activation And DI

- Add activation event matcher.
- Add service token structs and scoped service container.
- Migrate Writer markdown and Diagram SDN services first.
- Add capability checks for file, UI, DB, and process services.

## Slice 3: AOP Hooks

- Add command, document-save, render, diagnostics, lifecycle, and invalidation hook contracts.
- Add deterministic aspect ordering.
- Add undo/redo and telemetry as built-in aspects.

## Slice 4: Office Suite Migration

- Migrate Slides, Sheets, Dashboard, DB Admin, and Designer to contribution/service contracts.
- Add SDN diagram shape/location/style contributions.
- Add HTML Designer tool contributions.

## Slice 5: External Adapter

- Map VS Code extension features to Simple contribution points where practical.
- Keep adapter code outside the common contracts.

## Verification

- Add system tests for manifest validation, activation, DI capability enforcement, aspect ordering, and invalidation.
- Add perf evidence for warm manifest load and command dispatch overhead.

