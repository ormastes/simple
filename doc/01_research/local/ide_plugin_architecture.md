<!-- codex-research -->
# Local Research: IDE Plugin Architecture

## Scope

User request: make the Simple IDE and Office suite architecture plugin-based like VS Code and Eclipse, with MDSOC+ layering, dependency injection, and AOP-style plugin connection points.

This research covers architecture only. It does not claim the plugin kernel is implemented yet.

## Current Repo Surfaces

Relevant existing paths:

- `src/app/vscode_extension/` already packages an editor extension lane.
- `src/app/ide/feature_report.spl` reports IDE feature inventory.
- `src/app/office/` owns Office plugin/catalog behavior used by markdown writer, slides, sheets, dashboard, DB admin, and designer slices.
- `doc/07_guide/ui/md_wysiwyg_graphical_render.md` documents markdown-to-styled-HTML-to-Engine2D rendering.
- `doc/07_guide/api/sdn_graph.md` documents SDN graph syntax, CSS labels, weaving, and markdown embedding.
- `doc/04_architecture/ui/ui_web_protocol.md` already defines capability-gated UI protocol concerns.
- `doc/04_architecture/ui/ui_access_protocol.md` defines a shared protocol for UI inspection and plugin/skill flows.
- `doc/04_architecture/ui/ui_test_architecture.md` includes Draw IR inspection extension concepts.

## Current Shape

The repo has many plugin-like pieces, but they are not yet unified behind one kernel:

- Declarative contributions exist as catalogs, manifests, guides, and feature reports.
- Runtime behavior is split across IDE, Office, UI, web, markdown, SDN, and VS Code extension paths.
- Capability checks exist in the UI protocol but are not yet the central dependency model for Office/IDE plugins.
- There is no single architecture doc that defines plugin lifecycle, contribution registry, service registry, activation policy, aspect hooks, or MDSOC visibility.

## Gaps To Close

- A stable manifest schema for IDE/Office plugins.
- A contribution registry that is cheap to load at startup.
- A service registry for DI with explicit capabilities and scopes.
- A limited AOP hook system for cross-cutting concerns: telemetry, undo/redo, autosave, validation, permission checks, render invalidation, and diagnostics.
- Host separation for UI-local plugins, workspace plugins, and headless/document plugins.
- Cache and invalidation rules for plugin manifests, SDN diagrams, markdown HTML render products, and UI document models.

## MDSOC Fit

Recommended common nodes:

- `src/lib/common/ide/plugin_manifest.spl` for manifest structs and validation.
- `src/lib/common/ide/plugin_contribution.spl` for contribution contracts.
- `src/lib/common/ide/plugin_service.spl` for service tokens and DI lookup.
- `src/lib/common/ide/plugin_aspect.spl` for ordered hook contracts.
- `src/lib/common/ide/plugin_capability.spl` for capability grants.

Recommended app-owned runtime nodes:

- `src/app/ide/plugin_kernel/registry.spl`
- `src/app/ide/plugin_kernel/activation.spl`
- `src/app/ide/plugin_kernel/service_container.spl`
- `src/app/ide/plugin_kernel/aspect_chain.spl`
- `src/app/ide/plugin_kernel/host_router.spl`

Office apps should remain virtual capsules over the common contracts, not private forks of the plugin model.

