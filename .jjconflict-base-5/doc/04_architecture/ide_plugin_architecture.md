<!-- codex-architecture -->
# IDE Plugin Architecture

## Status

Proposed.

## Goal

Make the Simple IDE and Office suite plugin-based like VS Code and Eclipse, but Simple-native: MDSOC+ layers, declarative contributions, scoped dependency injection, and constrained AOP hooks.

## Reference Model

Simple adopts these proven ideas:

- VS Code: manifests, contribution points, activation events, host placement, lazy loading, and extension host stability boundaries.
- Eclipse: extension points, extension registry, registry listeners, dynamic invalidation, bundles/services as a component model.

Simple does not adopt JavaScript extension execution, Java classloaders, OSGi bundle mechanics, or XML plugin descriptors.

## Layer List

| Layer | Path | Responsibility |
| --- | --- | --- |
| Common contracts | `src/lib/common/ide/` | Manifest, contribution, service, aspect, capability structs and traits |
| Plugin kernel | `src/app/ide/plugin_kernel/` | Registry, activation, service container, aspect chain, host router |
| IDE host | `src/app/ide/` | Workspace lifecycle, command dispatch, feature report, IDE UI integration |
| Office capsules | `src/app/office/` | Markdown/Writer, Calc, Impress/PPT, Draw/SDD, Designer, Base, Math, Mail, Planner, dashboard, DB admin plugin capsules |
| UI protocol | `src/lib/common/ui/`, `src/app/ui.web/` | Capability-gated UI access and render surfaces |
| Document formats | `src/lib/common/markdown/`, SDN graph docs and parsers | Markdown, HTML render, SDN diagram/document payloads |
| External extension adapters | `src/app/vscode_extension/` | VS Code bridge consuming the same common contracts where possible |

## Tree Encapsulation

`src/lib/common/ide/` is the only shared contract layer. Sibling plugins must not import each other's private code. Office plugins connect through contributions and service tokens:

- Markdown/Writer provides Markdown document, generated HTML render, block/table editing services.
- Impress/PPT provides Markdown deck, slide page, layout, and presentation services.
- Calc provides grid, formula, chart, and import/export services.
- Draw/SDD provides SDN graph, shape, connector, layout, and export services.
- Designer provides HTML/UI surface, CSS, component tree, constraint/layout, and asset services.
- Base provides table/database readback, import, and admin services.
- Math provides formula and MathML render services.
- Mail provides message, folder, and compose services.
- Planner provides task, board, calendar, timeline, and list services.

Each capsule owns its internal model and exposes only declared services.

## Contribution Points

Initial contribution point set:

- `commands`
- `menus`
- `views`
- `customEditors`
- `documentKinds`
- `renderers`
- `importers`
- `exporters`
- `diagnosticProviders`
- `diagramShapeKinds`
- `designerTools`
- `sheetFunctions`
- `slideLayouts`
- `aspectHooks`
- `services`

Contributions are loaded from plugin manifests and indexed before plugin activation.

## Activation Events

Initial activation event set:

- `onCommand:<id>`
- `onDocumentKind:<kind>`
- `onCustomEditor:<kind>`
- `onView:<id>`
- `onRenderer:<id>`
- `onService:<token>`
- `onStartupFinished`
- `onWorkspaceContains:<pattern>`

Activation must be lazy. Startup reads manifests and builds indexes only.

## Dependency Injection

DI is a scoped service registry:

- Service tokens are declared in manifests.
- Providers bind a token to a trait implementation during activation.
- Consumers declare required and optional tokens.
- The host injects a scoped `PluginContext` containing only approved services.
- Privileged services require capability grants.

Scopes:

- `global` for immutable host metadata and stable registries.
- `workspace` for file/project services.
- `document` for editor-specific models.
- `surface` for UI surface services.
- `request` for command/render invocation state.

## AOP Hooks

AOP is constrained to declared aspect hooks. There is no arbitrary runtime monkey-patching.

Aspect points:

- `before_command`, `around_command`, `after_command`
- `before_document_save`, `after_document_save`
- `before_render`, `after_render`
- `on_diagnostic_publish`
- `on_plugin_activate`, `on_plugin_deactivate`
- `on_resource_invalidated`

Ordering:

1. Capability/security aspects.
2. Validation aspects.
3. Undo/redo transaction aspects.
4. Plugin aspects.
5. Telemetry/diagnostic aspects.

Failure semantics: a failed `before_*` hook cancels the operation; a failed `after_*` hook records diagnostics but does not roll back completed work unless the hook owns the transaction.

## Public Surface Matrix

| Raw layer | Manifest node | Service node | Aspect node | Capability node |
| --- | --- | --- | --- | --- |
| Office capsule | public to plugin kernel | public provider/consumer declarations | public declared hooks only | public required grants |
| IDE host | public registry query facade | public scoped container facade | public aspect dispatch facade | public capability policy facade |
| UI protocol | public contribution render ids | public surface/document services | public render hooks | public UI mutation grants |
| External adapter | public manifest translation | public adapter services | no private host hooks | public adapter grants |

## Startup And Hot Paths

Startup:

1. Read built-in plugin manifest cache.
2. Validate manifests and contribution schema.
3. Build contribution index and activation trigger index.
4. Do not activate plugins unless startup contribution requires it.

Hot command dispatch:

1. Resolve command id in contribution index.
2. Activate owning plugin if needed.
3. Build request service scope.
4. Run aspect chain.
5. Invoke command service.
6. Publish diagnostics and invalidation events.

Hot render path:

1. Resolve renderer by document kind or custom editor.
2. Reuse cached document/render services.
3. Run render aspects.
4. Emit UI protocol patches or HTML/Engine2D output.

## Cache And Invalidation

Caches:

- Manifest index keyed by plugin id, version, manifest hash.
- Contribution index keyed by contribution point and id.
- Service binding index keyed by service token and scope.
- Aspect chain keyed by point, priority, plugin id, generation.
- Document render cache keyed by document uri, version, renderer id, style hash.
- SDN diagram layout cache keyed by graph hash, shape schema version, style hash.

Invalidation:

- Manifest change invalidates contribution, service, and aspect indexes.
- Document edit invalidates document render and diagnostics.
- SDN schema/style change invalidates diagram layout and export cache.
- Capability policy change deactivates affected plugins and clears service scopes.

## Migration Sequence

1. Add common manifest/contribution/service/aspect/capability structs.
2. Add plugin kernel registry and manifest cache for built-in Office plugins.
3. Migrate Office feature catalog entries into declarative contribution points.
4. Add DI service tokens for Markdown/Writer markdown, Impress/PPT deck,
   Calc grid, Draw/SDD graph, Designer HTML surface, Base table, Math formula,
   Mail message, and Planner task services.
5. Add command/document/render aspect hooks with deterministic ordering.
6. Route VS Code adapter and IDE feature report through the same registry.
7. Add dynamic plugin invalidation only after built-in plugins are stable.

## Requirement Trace

| Requirement | Architecture evidence |
| --- | --- |
| REQ-IPA-001 | Reference model, layer list, contribution points, activation events |
| REQ-IPA-002 | Tree encapsulation and public surface matrix |
| REQ-IPA-003 | Service container |
| REQ-IPA-004 | Contribution points |
| REQ-IPA-005 | Aspect hooks and ordering/failure semantics |
| REQ-IPA-006 | Office capsules, tree encapsulation, startup and hot paths |
| REQ-IPA-007 | Layer list, tree encapsulation, public surface matrix |
| REQ-IPA-008 | Office action bridge coverage in `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl` |
| NFR-IPA-001 | Startup manifest cache path |
| NFR-IPA-002 | Lazy activation path |
| NFR-IPA-003 | Hot command dispatch path |
| NFR-IPA-004 | Cache and invalidation model |
| NFR-IPA-005 | Capability model and public surface matrix |
| NFR-IPA-006 | IDE Office feature-check contract in `doc/07_guide/app/ide_office_plugin_suite.md` |
| NFR-IPA-007 | Migration sequence step 7 defers dynamic invalidation |
