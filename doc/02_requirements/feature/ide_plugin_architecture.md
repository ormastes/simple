# IDE Plugin Architecture Requirements

## Selection

Selected feature option: **Option C, Plugin Kernel With DI And AOP**, delivered in slices:
manifest registry first, scoped DI second, constrained AOP hooks third.

## Requirements

- REQ-IPA-001: The IDE and Office suite MUST use a plugin-kernel architecture with declarative manifests, contribution points, activation events, and host routing modeled after VS Code and Eclipse, without adopting JavaScript extension execution, OSGi, Java classloaders, or XML descriptors.
- REQ-IPA-002: `src/lib/common/ide/` MUST be the shared contract layer for manifests, contributions, services, capabilities, and aspect hooks; sibling plugins MUST NOT import each other's private implementation modules.
- REQ-IPA-003: The kernel MUST support scoped dependency injection through named service tokens for global, workspace, document, and plugin scopes.
- REQ-IPA-004: Plugin behavior MUST connect through declared contribution points including commands, menus, views, custom editors, document kinds, renderers, importers, exporters, diagnostics, diagram shape kinds, designer tools, sheet functions, slide layouts, services, and aspect hooks.
- REQ-IPA-005: Aspect hooks MUST be host-owned, ordered, capability-gated extension points for command dispatch, document save, rendering, diagnostics, telemetry, undo/redo, and persistence.
- REQ-IPA-006: The Office suite plugins MUST expose Writer Markdown, Impress Markdown/PPT HTML, Calc, SDD Diagram Draw, HTML UI Designer, Base, Math, Mail, Planner, Counter, and Launcher through the plugin kernel without host GUI/browser/network dependencies in feature checks.
- REQ-IPA-007: The architecture MUST preserve MDSOC+ boundaries: plugins are virtual capsules with manifests, ports, capabilities, lifecycle, and internal state ownership.
- REQ-IPA-008: The LLM-facing Office catalog MUST advertise only actions with schemas and recognized Office bridge dispatch coverage.

