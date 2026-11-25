# Architecture: A2UI and Dynamic App Interfaces (MDSOC+)

**Feature:** `a2ui_dynamic_app_interfaces`  
**Design Doc:** [a2ui_dynamic_app_interfaces.md](../05_design/a2ui_dynamic_app_interfaces.md)

## 1. Layering & Ownership Boundaries

```
+-----------------------------------------------------------------------+
|  App Adapters & Trusted Policies (Caret: src/app/llm_caret/a2ui/,     |
|  ClockApp: src/os/apps/clock/clock_a2ui.spl, *.authority.sdn)         |
+-----------------------------------+-----------------------------------+
                                    | typed descriptors & owner snapshots
+-----------------------------------v-----------------------------------+
|  Shared App Interface (`src/lib/common/app_interface/`)               |
|  - contracts.spl: resources, queries, commands, revisions, schemas    |
|  - authority.spl: default-deny policy, region ceilings, HMAC grants   |
|  - query_ir.spl: restricted SPL -> QueryIR, BoundedChangeJournal      |
|  - runtime.spl: /view vs /draft, dynamic composition, hot-swap leases |
+-----------------------------------+-----------------------------------+
                                    | typed surface ops & keyed collections
+-----------------------------------v-----------------------------------+
|  Shared A2UI Semantics (`src/lib/common/ui/a2ui/`)                    |
|  - types.spl / catalog.spl / express_grammar.spl (shared scalar VM)   |
|  - screen_table.spl (strict_v1 raw SDN table + opaque c_<hex> keys)   |
|  - surface_state.spl (isolated registry, dep index, UITree, JSON v1.0)|
+-----------------------------------+-----------------------------------+
                                    | qualified SimpleUI WidgetNode/UITree
+-----------------------------------v-----------------------------------+
|  Existing SimpleUI, Crypto, Parse VM, & Aspect Dynload Lifecycle      |
|  `common.ui.widget`, `common.sdn.strict_v1`, `common.json.parser`,    |
|  `common.structural.parse.grammar_cpu_v1`, `common.crypto.hmac`,      |
|  `common.aspect_dynload_lifecycle_v1`                                 |
+-----------------------------------------------------------------------+
```

## 2. Key Architectural Invariants

1. **Common code stays app-agnostic:** `src/lib/common/ui/a2ui/` and `src/lib/common/app_interface/` have zero dependencies on `app.llm_caret` or `os.apps.*`.
2. **Authority never lives in screen tables:** `*.screen.sdn` contains only layout, bindings, and region requests; effective rights are the intersection of authenticated principal HMAC grants, trusted `*.authority.sdn` region ceilings, resource field policies, and release audiences.
3. **Hot swap vs dynamic UI composition:** Screen edits increment `composition_revision` without touching executable code. Handler code swaps reuse `aspect_dynload_lifecycle_v1` quiescence/reclamation leases at request boundaries under `HandlerGenerationOwner` while preserving the stable Caret main loop (`cs_main.spl`), ECS World, drafts, and surface state.
4. **One App, One Host Interface:** `CaretA2uiHost` and `clock_mount_a2ui_surface` share the exact same backend-independent `A2uiSurfaceRegistry` and `UITree` lowering across TUI, GUI, web, headless, and SimpleOS targets.
