# Domain Research: A2UI v1.0 and Language-Integrated Dynamic App Interfaces

**Feature:** `a2ui_dynamic_app_interfaces`  
**Upstream A2UI Baseline:** `a2ui-project/a2ui` at `1dbe86a942579cc83a1d657213f0db3b881632ae` (wire `"1.0"`)  
**Full Design & Bibliography:** [a2ui_dynamic_app_interfaces.md §18 & §24](../../05_design/a2ui_dynamic_app_interfaces.md)

## 1. Upstream A2UI Contract

- Wire protocol version `"1.0"` defines 6 agent-to-renderer operations: `createSurface`, `updateComponents`, `updateDataModel`, `deleteSurface`, `callRendererFunction`, `agentFunctionResponse`, plus renderer-to-agent `action` envelopes (`name`, `surfaceId`, `sourceComponentId`, `timestamp`, `context`).
- `Express.g4` is an authoring/inference syntax compiled to the same typed protocol operations. Custom formats (such as Simple's flat `express_sdn_table_v1`) lower directly to those operations without forcing external renderers to understand SDN.
- Key semantic invariants: `_` means omitted argument (distinct from explicit `null`); `updateComponents` is complete replacement; `updateDataModel` replaces/deletes exact paths; `callRendererFunction` enforces `allowedCallers` and `requiresUserActivation`.

## 2. Academic & Systems Foundations

- **Language-Integrated Query & Tierless Typing (LINQ / Links / Ur/Web / Hilda):** Typed query expressions normalize into closed `QueryIR` plans (`Filter`, `Project`, `OrderBy`, `Page`) while mutations execute through explicitly authorized typed commands with precondition/revision checks.
- **Incremental Views & Subscriptions (DBSP / Incremental Lenses):** Independent sequence cursors in `BoundedChangeJournal` ensure slow or multiple subscribers receive deletions/updates without destructive queue draining.
- **Declarative Access Control & Information Flow (WebDSL / UrFlow / SIF / Zanzibar):** Separate trusted policy (`*.authority.sdn`) with default-deny rules, region capability ceilings, distinct field sets (`named_query_use_fields`, `dynamic_query_fields`, `release_fields`), release audiences, and policy-revision cache keys.
- **Dynamic UI Composition & Request-Boundary Code Replacement (SUPPLE / Servlet-style Leases):** UI layout and query composition happen as versioned data updates during normal execution; actual handler code replacement uses request-boundary `aspect_dynload_lifecycle_v1` leases with ABI checks and quiescence reclamation.
