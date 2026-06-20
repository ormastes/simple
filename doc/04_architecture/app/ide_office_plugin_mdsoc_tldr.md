# IDE Office Plugin MDSOC TLDR

Purpose: make the IDE Office suite plugin-based like VS Code/Eclipse without
adding a speculative framework.

Core decision: the plugin boundary is the existing pure metadata/action surface:
`src/app/office/plugins.spl`, `src/app/office/llm_catalog.spl`,
`src/app/ide/plugin_manifest.spl`, `src/app/office/mod.spl`, and
`src/app/office/launcher.spl`.

Layering:

- IDE shell: `src/app/ide/feature_report.spl`,
  `src/app/ide/plugin_manifest.spl`
- Plugin metadata: `src/app/office/plugins.spl`,
  `src/app/office/llm_catalog.spl`
- Action bus: `src/app/office/mod.spl`, `src/app/office/launcher.spl`
- App modules: `src/app/office/**`
- Shared services: `src/lib/editor/services/sdn_graph.spl` and Markdown helpers

DI rule: `office_action_dispatch_with_context(context, source)` accepts an
explicit `OfficePluginContext` and rejects wrong action/source-format pairings.
No service locator or container yet.

AOP rule: stale rejection, allowlists, schemas, telemetry, and evidence strings
wrap dispatch/reporting. App modules should not duplicate those checks.

Draw/Designer rule: keep SDD/SDN graph behavior in
`src/lib/editor/services/sdn_graph.spl`; do not fork a diagram grammar.

Next paths to inspect:

- `doc/04_architecture/app/ide_office_plugin_mdsoc.md`
- `doc/07_guide/app/ide_office_plugin_suite.md`
- `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`
