# Module Surface Export Provenance Agent Tasks

## Frozen shared interfaces

`ModuleSurfaceExportOrigin`, `ModuleSurface.reexports`,
`module_surfaces_resolve_reexports`, `module_surface_export_origin`, and
`module_surface_resolve_key` are merge-owner controlled. Scenario steps and
helpers are frozen in the system-test plan.

## Lanes

| Lane | Scope | Sidecar |
|---|---|---|
| A | Surface structs, canonical key resolver, deterministic finalizer | Codex Spark or N/A |
| B | Explicit/aliased import consumer migration | Claude Haiku or N/A |
| C | Glob/package/multi-hop consumer migration | Claude Sonnet or N/A |
| D | Unit/system tests, generated manual, portability fixtures | Codex Spark or N/A |
| E | Stage 4 perf/RSS/fan-out evidence and fallback audit | Claude Haiku or N/A |
| F (future) | `ResolvedModuleGraph` nodes/edges, then symbol-body closure | separate approved phase |

Every implementation lane claims its bug/task record before editing and works
in an isolated workspace. Pure-Simple owners are changed before any Rust mirror;
Rust changes require a proven boundary gap plus paired parity tests.

## Sequencing

1. Merge A and its tests.
2. Merge B, then C; retain observable legacy fallback.
3. Merge D and regenerate/review the manual.
4. Run E once. Remove fallback only when count is zero and Stage 4 evidence is
   stable.
5. Defer F; do not widen the immediate fix into body-closure migration.

Merge owner: main integration agent. Final reviewer: best available
normal/highest-capability model. The reviewer owns interface consistency,
manual quality, exclusions, NFR evidence, and final done marks.
