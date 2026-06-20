<!-- codex-design -->
# Detail Design: IDE Plugin Architecture

## Proposed Types

Common contracts live under `src/lib/common/ide/`.

- `PluginManifest`: id, version, display name, engine range, host kinds, capabilities, activation events, contributions, services, aspect hooks.
- `PluginContribution`: contribution point, id, owner plugin, payload SDN/record, activation event.
- `PluginServiceToken`: stable service id, trait name, scope, capability requirements.
- `PluginServiceBinding`: token, provider plugin, factory id, lifecycle.
- `PluginAspectHook`: point, priority, owner plugin, capability requirements.
- `PluginCapabilityGrant`: capability id, scope, reason, optional resource pattern.
- `PluginGeneration`: registry generation used for invalidation.

Runtime kernel lives under `src/app/ide/plugin_kernel/`.

- `PluginRegistry`: validates manifests and builds contribution indexes.
- `ActivationManager`: maps activation events to plugin activation.
- `ServiceContainer`: builds scoped DI contexts.
- `AspectChain`: resolves hooks and executes deterministic chains.
- `HostRouter`: places plugins in UI, workspace, headless, or external adapter hosts.
- `InvalidationBus`: publishes registry, document, resource, and capability invalidation.

## Manifest Shape

Manifests should be SDN-native so Office documents and diagrams can reuse the same parser family.

Required fields:

- `id`
- `version`
- `engine`
- `host_kind`
- `activation_events`
- `contributes`

Optional fields:

- `services`
- `aspects`
- `capabilities`
- `dependencies`

## Service Scope Rules

- `global`: immutable registries and host metadata.
- `workspace`: file tree, project config, build/test services.
- `document`: markdown, slide, sheet, diagram, and designer document models.
- `surface`: UI surface access, selection, focus, and capture.
- `request`: command/render invocation state.

Plugin code receives a `PluginContext` with only the scopes and tokens it declared.

## Aspect Rules

Aspect hooks are not general method interception. They are host-owned extension points with strict contracts:

- Hook payloads are typed records.
- Hooks return `Result<T, PluginError>`.
- Ordered chains are stable by priority, plugin id, then manifest order.
- Security and validation hooks run before plugin hooks.
- Telemetry hooks cannot change command/render outputs.

## Office Suite Mapping

| Office area | Plugin service tokens | Contribution points |
| --- | --- | --- |
| Writer | markdown document, block edit, table edit, HTML render | `customEditors`, `renderers`, `commands`, `exporters` |
| Slides | deck model, slide layout, presenter view | `slideLayouts`, `views`, `commands`, `exporters` |
| Sheets | grid model, formula engine, chart model | `sheetFunctions`, `customEditors`, `commands`, `exporters` |
| Diagram | SDN graph model, shape registry, layout, export | `diagramShapeKinds`, `renderers`, `commands`, `exporters` |
| Designer | HTML component tree, CSS style model, constraints, assets | `designerTools`, `customEditors`, `views`, `renderers` |
| DB Admin | connection, schema browser, SQP query, table viewer | `views`, `commands`, `services`, `diagnosticProviders` |

## Verification Plan

First implementation slice should add SPipe coverage for:

- manifest validation accepts built-in plugin manifests;
- duplicate contribution ids are rejected;
- lazy activation occurs on command/document event;
- DI rejects undeclared service tokens;
- privileged services require capability grants;
- aspect order is deterministic;
- registry generation changes invalidate cached lookup handles.

