<!-- codex-research -->
# Domain Research: IDE Plugin Architecture

## Sources

- VS Code Extension Host: https://code.visualstudio.com/api/advanced-topics/extension-host
- VS Code Contribution Points: https://code.visualstudio.com/api/references/contribution-points
- VS Code Extension Manifest: https://code.visualstudio.com/api/references/extension-manifest
- VS Code Activation Events: https://code.visualstudio.com/api/references/activation-events
- Eclipse runtime plug-in model: https://help.eclipse.org/latest/topic/org.eclipse.platform.doc.isv/guide/runtime_model.htm
- Eclipse `IExtensionRegistry`: https://help.eclipse.org/latest/topic/org.eclipse.platform.doc.isv/reference/api/org/eclipse/core/runtime/IExtensionRegistry.html
- Eclipse RT/Equinox charter: https://projects.eclipse.org/content/eclipse-rt-charter

## VS Code Findings

VS Code separates declarative extension metadata from executed extension code:

- Extension manifests declare identity, compatibility, contributions, and activation events.
- Contribution points register commands, menus, custom editors, views, languages, grammars, themes, debuggers, notebooks, tasks, and related UI/workspace capabilities.
- Activation events lazily load extensions when a command, language, file system, custom editor, or other trigger is used.
- Extension hosts isolate extension execution from UI work and use placement rules such as UI, workspace, local, remote, and web.
- Stability guidance centers on preventing extensions from hurting startup, slowing UI operations, or mutating UI internals directly.

Simple should copy the separation of declaration, activation, and host placement. It should not copy the JavaScript-specific runtime.

## Eclipse Findings

Eclipse separates extension registry metadata from service/runtime wiring:

- The runtime plug-in model centers on plug-ins that declare extension points and extensions.
- `IExtensionRegistry` is the master list of namespaces, extension points, and extensions.
- Registry objects can become invalid when plug-ins update or uninstall, so dynamic-aware code must handle invalidation and registry change events.
- Equinox/OSGi supplies a component model with bundles and services, including infrastructure useful to Eclipse applications.

Simple should copy the extension point registry, service registry, lazy activation, and invalidation model. It should not copy Java classloaders, OSGi bundle mechanics, or XML plugin descriptors.

## DI Implication

Plugin connection should use explicit service tokens instead of direct imports between sibling plugins:

- A plugin provides services under names and traits.
- A plugin consumes services by declaring required and optional tokens.
- The host builds a scoped service container for activation.
- Capability checks gate privileged tokens such as file I/O, UI mutation, command execution, process launch, network, and database access.

## AOP Implication

Cross-cutting behavior should be modeled as ordered aspect hooks, not hidden global interception:

- `before_command`, `around_command`, `after_command`
- `before_document_save`, `after_document_save`
- `before_render`, `after_render`
- `on_diagnostic_publish`
- `on_plugin_activate`, `on_plugin_deactivate`
- `on_resource_invalidated`

Aspects must be deterministic, capability-gated, and observable. They must not rewrite arbitrary plugin internals.

## Recommendation

Build a Simple plugin kernel that combines:

- VS Code-style declarative contribution points and activation events.
- Eclipse-style extension registry and registry invalidation.
- OSGi-style service lookup adapted to Simple traits and MDSOC visibility.
- A constrained AOP hook chain for Office/IDE cross-cutting concerns.

