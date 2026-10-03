# Collection planner driver session

Authored manual, 2026-10-03. Source: `test/01_unit/compiler/driver/collection_planner_session_spec.spl`. This document is not generated runner output. The six scenarios have not been executed in this session.

Partial traceability: REQ-003 (registry lifecycle and invalidation), REQ-007 (shared HIR admission boundary). These cases exercise production driver, parser, binder, and analysis APIs with explicitly constructed HIR modules; they do not establish executable physical plans or backend parity.

| Scenario | Setup and action | Observable assertion |
|---|---|---|
| Default authority | Create a driver and admit the HIR phase without configuring metadata. | Configuration remains false; admission succeeds without registries or analysis snapshots. |
| Per-module capture | Configure valid empty metadata and retain two distinct empty HIR modules. | Both analyses are retained; metadata version and structural validity are reported; no plans are invented. |
| Invalidation | Analyze with an old metadata version, reconfigure, analyze again, then reject HIR admission. | Reconfiguration immediately clears snapshots; the next snapshot uses the new version; rejected admission clears snapshots again. |
| Failed reconfiguration | Configure valid metadata, then supply an invalid schema. | The prior registry and analyses are cleared; an error is retained; subsequent admission fails. |
| Shared entrypoints | Configure invalid metadata on separate ordinary and explicit compilation drivers. | Both monomorphization entrypoints return false and record errors before proceeding. |
| Incomplete HIR | Retain one module while the recorded module count is two. | Admission fails, publishes no analyses, and reports `collection-analysis-incomplete-hir`. |

The empty operations list deliberately exercises lifecycle without granting any operation authority. Production bindings are scoped by module path and validated against actual declarations before snapshots are published. Source loading is explicit configuration, with bounded parser/binder validation; no filesystem or environment discovery is performed per function.

Remaining evidence includes configured nonempty operation analysis through compiled programs, physical lowering, interpreter/native parity, and measured resource limits. An analysis snapshot is advisory evidence, not authorization to rewrite.
