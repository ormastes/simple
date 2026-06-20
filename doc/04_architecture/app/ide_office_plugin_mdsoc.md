<!-- codex-architecture -->
# IDE Office Plugin MDSOC Architecture

## Status

Proposed architecture for continuing the IDE Office suite hardening work.

## Context

The current suite already exposes most of the requested Office surface through
small pure modules:

- IDE feature and product reports: `src/app/ide/feature_report.spl`
- IDE plugin metadata: `src/app/ide/plugin_manifest.spl`
- IDE capability registry: `src/app/ide/capabilities.spl`
- Office app catalog: `src/app/office/llm_catalog.spl`
- Headless Office action bridge: `src/app/office/mod.spl`
- Launcher: `src/app/office/launcher.spl`
- Markdown/Writer: `src/app/office/md_wysiwyg.spl`,
  `src/app/office/word/html_render.spl`
- Impress/PPT: `src/app/office/slides/html_render.spl`
- Designer/Figma-like HTML editor: `src/app/office/ui_editor.spl`
- Draw/draw.io-like diagram editor: `src/lib/editor/services/sdn_graph.spl`
- Mail, Planner, Counter: `src/app/office/mail/`,
  `src/app/office/planner/`, `src/app/office/counter.spl`

External architecture models used:

- VS Code separates manifest contribution points, activation events, and API
  command registration. The Simple equivalent is a pure manifest/catalog first,
  then action dispatch only when called.
- Eclipse plug-ins use extension points and service-oriented composition. The
  Simple equivalent is a typed contribution catalog plus dependency-injected
  service records, not direct sibling imports.
- Eclipse e4 DI avoids singleton/global lookup by injecting services from a
  context. The Simple equivalent is explicit context records passed into app
  actions.
- AspectJ modularizes cross-cutting behavior such as error handling, monitoring,
  logging, debugging, and synchronization. The Simple equivalent is MDSOC
  feature transforms or wrapper functions around dispatch, not app-owned copies
  of those checks.

References:

- https://code.visualstudio.com/api/get-started/extension-anatomy
- https://code.visualstudio.com/api/references/contribution-points
- https://wiki.eclipse.org/Eclipse4/RCP/Dependency_Injection
- https://eclipse.dev/aspectj/

## Decision

The IDE Office suite should remain plugin-based, but the plugin boundary is the
existing pure metadata/action surface, not a new framework:

1. `src/app/office/plugins.spl` owns plugin descriptors and contribution shape.
2. `src/app/office/llm_catalog.spl` owns LLM-readable capabilities and actions.
3. `src/app/ide/plugin_manifest.spl` owns IDE-visible plugin manifest checks.
4. `src/app/office/mod.spl` owns action dispatch and fail-closed input routing.
5. Individual Office apps own document semantics and rendering only.
6. Cross-cutting concerns use DI/AOP-style wrappers at dispatch/reporting
   boundaries instead of being copied into every app.
7. `office_catalog_dispatch_probe()` must exercise catalog actions through
   `OfficePluginContext` using each row's explicit `source_format`, so catalog
   component, source-format, and evidence drift is caught by the dispatcher
   gate. The probe treats `unknown-action`,
   `context-mismatch`, and `source-format-mismatch` as missing catalog actions.
   `office_llm_catalog_validate` rejects source formats outside the supported
   Office substrate allowlist.

## Layer List

| Layer | Path | Responsibility |
| --- | --- | --- |
| IDE shell | `src/app/ide/` | Feature reports, plugin manifest readback, TUI/GUI parity probes |
| Plugin metadata | `src/app/office/plugins.spl`, `src/app/office/llm_catalog.spl` | Contribution descriptors, app/action catalog, evidence keys |
| Office action bus | `src/app/office/mod.spl`, `src/app/office/launcher.spl` | Command normalization, action dispatch, app launch routing |
| Office apps | `src/app/office/**` | Markdown, Writer, Calc, Impress, Draw bridge, Designer, Base, Math, Mail, Planner, Counter |
| Shared editor services | `src/lib/editor/services/**` | SDN/SDD graph, Markdown services, command/search/LSP services |

## Tree Encapsulation

- `src/app/ide/` may read Office plugin metadata and feature-check summaries.
  It must not import app-private document models except through probe modules.
- `src/app/office/llm_catalog.spl` may name app owner modules and actions. It
  must not call rendering/editing functions.
- `src/app/office/mod.spl` is the only headless action router. New actions go
  through it so stale rejection, schemas, and AOP-style telemetry stay central.
- `src/app/office/*` app modules may import shared services from
  `src/lib/editor/services/**` but should not import sibling app internals.
- `src/lib/editor/services/sdn_graph.spl` remains the common SDD graph substrate
  used by Draw and Designer export. It must not depend on IDE or Office apps.

## Common Tree Nodes

| Common node | Current path | Consumers |
| --- | --- | --- |
| Plugin descriptor | `src/app/office/plugins.spl` | IDE manifest, launcher, feature reports |
| LLM catalog | `src/app/office/llm_catalog.spl` | IDE feature report, source-format metadata, agent tooling, specs |
| Action dispatcher | `src/app/office/mod.spl` | System specs, headless automation |
| SDD/SDN graph | `src/lib/editor/services/sdn_graph.spl` | Draw, Designer export, docs diagrams |
| Markdown render contract | `src/app/office/md_wysiwyg.spl`, `src/app/office/word/html_render.spl` | Markdown preview, Writer, PPT source workflows |

## Public Surface To Next Layer

| From | Public surface | Next layer |
| --- | --- | --- |
| IDE shell | `ide_feature_check_report`, `ide_plugin_manifest_probe` | Plugin metadata |
| Plugin metadata | `office_llm_feature_catalog`, `office_plugin_manifest` | Office action bus |
| Office action bus | `office_action_dispatch`, launcher `open_*` actions | Office apps |
| Office apps | Render/edit functions with guarded source input | Shared editor services |
| Shared editor services | SDN/SDD parse, render, inspect, edit helpers | App renderers |

## MDSOC Matrix

| Raw layer | Plugin descriptor | LLM catalog | Action dispatcher | SDD/SDN graph |
| --- | --- | --- | --- | --- |
| IDE shell | Public to parent: manifest readback. Public to next sibling: no direct app calls. | Public to parent: feature summary. Public to next sibling: read-only names/counts. | No direct ownership. | No direct mutation; Draw probe only. |
| Plugin metadata | Owns descriptor shape. | Owns app/action/evidence rows. | Names actions only. | Names owner module only. |
| Office action bus | Reads descriptors. | Reads action names/schema policy. | Owns dispatch, validation, fail-closed routing. | Calls through Draw/Designer actions only. |
| Office apps | Do not mutate descriptor shape. | May be named by catalog. | Expose minimal action functions. | Draw/Designer consume graph services. |
| Shared editor services | No plugin imports. | No catalog imports. | No dispatch imports. | Owns graph parse/edit/render contract. |

## DI Model

Use explicit records when app actions need shared services:

- `OfficePluginContext`: app id, action id, source format, evidence key. The
  first code surface is `office_action_dispatch_with_context(context, source)`
  in `src/app/office/mod.spl`; legacy callers still use
  `office_action_dispatch(action, source)`. Non-empty source formats are
  checked against the action family and reject as `source-format-mismatch` when
  a caller claims the wrong substrate.
- `OfficeRenderServices`: Markdown renderer, SDD renderer, HTML escape policy.
- `OfficeAuditServices`: optional log/metric/stale-reject counters.

The default entrypoint may build the records in one place. Tests may pass small
records directly. Do not add a container or service locator until two real
callers need runtime replacement.

## AOP Model

Cross-cutting behavior belongs around the dispatcher and report builders:

- stale-source rejection
- input schema validation
- action allowlist checks
- telemetry/counting
- feature-check evidence strings
- debug capture hooks

These are MDSOC feature transforms or small wrappers. App modules should not
duplicate them.

## Migration Sequence

1. Keep current pure manifest/catalog/action surfaces as the plugin boundary.
2. Extend `OfficePluginContext` only when the next action needs another shared
   service.
3. Move duplicated validation into dispatcher wrappers before adding new app
   actions.
4. Keep Draw/Designer on `src/lib/editor/services/sdn_graph.spl`; do not fork a
   separate diagram grammar.
5. Update `doc/07_guide/app/ide_office_plugin_suite.md` and the IDE system spec
   whenever plugin names, actions, schemas, or evidence keys change.
