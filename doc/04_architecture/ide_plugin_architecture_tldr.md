<!-- codex-architecture -->
# TL;DR: IDE Plugin Architecture

Build one Simple-native plugin kernel for IDE and Office.

Core decision:

- Use VS Code-style manifests, contribution points, activation events, lazy plugin activation, and host placement.
- Use Eclipse-style extension registry, service registry, registry listeners, and invalidation.
- Keep Simple MDSOC rules: shared contracts in `src/lib/common/ide/`,
  runtime kernel in `src/app/ide/plugin_kernel/`, and Office apps as virtual
  capsules: Markdown/Writer, Calc, Impress/PPT, Draw/SDD, Designer, Base, Math,
  Mail, Planner, dashboard, and DB admin.

DI:

- Plugins provide and consume explicit service tokens.
- The host injects scoped services through `PluginContext`.
- Privileged services require capability grants.

AOP:

- Only declared aspect hooks are allowed: command, document save, render, diagnostics, plugin lifecycle, and invalidation.
- Hook order is deterministic: security, validation, transaction, plugin, telemetry.

Startup:

- Read manifest cache, validate contributions, build indexes.
- Do not activate plugins on startup unless explicitly required.

Hot path:

- Resolve contribution, activate plugin if needed, build request scope, run aspect chain, invoke service.

Next files to create during implementation:

- `src/lib/common/ide/plugin_manifest.spl`
- `src/lib/common/ide/plugin_contribution.spl`
- `src/lib/common/ide/plugin_service.spl`
- `src/lib/common/ide/plugin_aspect.spl`
- `src/app/ide/plugin_kernel/registry.spl`
- `src/app/ide/plugin_kernel/service_container.spl`
