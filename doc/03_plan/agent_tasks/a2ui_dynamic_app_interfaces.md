# Agent Task Breakdown: A2UI and Dynamic App Interfaces

**Feature:** `a2ui_dynamic_app_interfaces`  
**Sidecar Lanes:** `N/A` (focused single-lane architecture & implementation planned and executed under high-capability review)  
**Merge Owner:** Primary implementation agent (`work/a2ui-dynamic-app-interfaces-20261125`)  
**Final Reviewer:** Exact-head self-review + GitHub `Code Idiom & Structural Ratchet Gates`

## Lanes & Ownership

1. **Lane A (Common A2UI & Parser Contracts):** `src/lib/common/ui/a2ui/*`, `src/lib/common/json/{tokenizer,parser}.spl`
2. **Lane B (Common App Interface, QueryIR, Authority & Hot Swap):** `src/lib/common/app_interface/*`, `src/lib/common/privilege/store.spl`, `src/app/simple_process_manager/{approval_broker,privilege_service}.spl`
3. **Lane C (Caret Suite & ClockApp Integration):** `src/app/llm_caret/a2ui/*`, `src/app/llm_caret/{cs_gui,cs_main}.spl`, `src/os/apps/clock/clock_a2ui.spl`
4. **Lane D (SPipe Docs, Specs, Manuals & Native Verification):** `doc/**`, `test/**`
