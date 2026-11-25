# Non-Functional Requirements: A2UI and Dynamic App Interfaces

**Feature:** `a2ui_dynamic_app_interfaces`  
**Design Doc:** [a2ui_dynamic_app_interfaces.md](../../05_design/a2ui_dynamic_app_interfaces.md)

## NFR Targets

- **NFR-A2UI-001 (Zero Steady-State Text Round-Trips):** Local rendering lowers parsed flat SDN tables and Express expressions directly to `A2uiSurfaceOp` and SimpleUI `WidgetNode`/`UITree` without re-emitting Express text or reparsing JSON.
- **NFR-A2UI-002 (Pre-Allocation Resource Admission):** Lexers, strict SDN, `ParseProgramV2`, bounded JSON (`max_source_bytes`, `max_tokens`, `max_depth`), query step budgets, and retained component caps reject oversized or deeply nested inputs before unbounded allocation.
- **NFR-A2UI-003 (Linear Snapshot Indexing & Cursor Isolation):** `caret_build_roster_snapshot` and `query_execute_authorized` index keys and pins via `Dict` lookups rather than nested scans; `BoundedChangeJournal` prevents slow subscribers from stealing removal events from peer cursors.
- **NFR-A2UI-004 (Shared Layering & Zero Caret Coupling):** `src/lib/common/ui/a2ui/` and `src/lib/common/app_interface/` contain zero Caret imports, zero `rt_*` direct calls (`direct-env-runtime-guard`), and remain under 800 lines per source file.
- **NFR-A2UI-005 (Cryptographic Authority & Default-Deny Security):** Grants are bound with canonical length-prefixed HMAC-SHA256 (`hmac_sha256_bytes`), verified against store membership, principal, surface, region ceiling, policy revision, expiry, and one-shot nonces; unknown command arguments (mass assignment) are rejected.
- **NFR-A2UI-006 (Request-Boundary Hot-Swap Lifetime Safety):** Code generation replacement delegates lifetime tracking to `std.common.aspect_dynload_lifecycle_v1`, ensuring in-flight and suspended async handlers finish on their pinned generation before reclamation while rejecting mismatched ABIs and stale surface commits.
