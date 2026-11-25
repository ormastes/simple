# Local Research: A2UI and Dynamic App Interfaces

**Feature:** `a2ui_dynamic_app_interfaces`  
**Reviewed Baseline:** `ormastes/simple` `release/1.0.0`  
**Design Doc:** [a2ui_dynamic_app_interfaces.md](../../05_design/a2ui_dynamic_app_interfaces.md)

## 1. Parser Infrastructure Audit

- `src/lib/common/structural/parse/parse_types.spl`: Provides `ParseSourceBlob` (flat `[u8]`), `ParseTokenArena` (SoA `(kind, start, count)`), and `ParseDiagnostic` without text copies per token.
- `src/lib/common/structural/parse/program_v1.spl`: Provides validated `ParseProgramV1` / `ParseProgramV2` instruction programs with literal tables and explicit resource budgets (`ParseProgramLimitsV1`).
- `src/lib/common/structural/parse/grammar_cpu_v1.spl`: Provides transactional scalar grammar VM (`parse_grammar_execute_v2`) with rollback checkpoints and strict EOF acceptance.
- `src/lib/common/sdn/strict_v1.spl`: Complete strict SDN v1 parser supporting anonymous root tables (`|col1, col2, ...|`), quoted cell escaping, duplicate-key rejection, and bounded depth/row/cell limits (`SdnStrictLimitsV1`).
- `src/lib/common/json/parser.spl` & `src/lib/common/json/tokenizer.spl`: `json_parse_strict_with_error` rejects duplicate object keys, and now `json_tokenize_bounded` + `json_parse_strict_bounded_with_error` enforce `max_source_bytes`, `max_tokens`, and `max_depth` before recursive descent.

## 2. UI, Privilege, and Lifecycle Infrastructure Audit

- `src/lib/common/ui/widget.spl`, `builder.spl`, `surface.spl`, `ui_identity.spl`: Shared `UITree`/`WidgetNode` semantic model and `SurfaceManager`; `a2ui_qualified_handle` extends identity with `(owner_id, wire_surface_id, surface_generation, component_id)` so colliding `root` and `refresh` wire IDs across apps remain isolated.
- `src/lib/common/aspect_dynload_lifecycle_v1.spl`: Canonical generation-bound execution leases (`aspect_dynload_lifecycle_create_v1`, `aspect_dynload_callback_begin_v1`, `aspect_dynload_around_suspend_v1`, `aspect_dynload_around_resume_v1`, `aspect_dynload_unload_v1`, `aspect_dynload_lease_complete_v1`, `aspect_dynload_lifecycle_reclaim_v1`), reused directly by `HandlerGenerationOwner`.
- `src/lib/common/privilege/` & `src/app/simple_process_manager/`: `approval_broker.spl` previously concatenated secrets instead of computing HMAC-SHA256 and omitted `level` in `_intent_equals`; `store.spl` lacked attenuated minting and untrusted decode separation; `privilege_service.spl` lacked store/caller/level checks on consumption. All three seams are hardened using `std.common.crypto.hmac.hmac_sha256_bytes`.

## 3. Application Seams: Caret Suite and ClockApp

- **Caret Suite (`src/app/llm_caret/`):** `cs_dashboard_model.spl` (`CsDashboard`, `CsAgent` with `-1` unavailable metric sentinels), `cs_gui.spl` (`cs_resolve_ui_mode`, session projection), `cs_main.spl` (stable TUI/CLI owner loop), `workbench/session_contract.spl` (`SessionId(value, generation)`, `ComposerDraft`, `Delivery`, `SessionControlLeaseV2`), `workbench/pane_binding.spl`, and `workbench/session_source.spl` (`send_draft_guarded`).
- **Second App Fixture (`src/os/apps/clock/clock.spl`):** `ClockApp` owns `ClockAppWorld` (ECS stopwatch and timer entities) and builds a `UISession`, ideal for validating non-Caret shared infrastructure reuse via `src/os/apps/clock/clock_a2ui.spl`.
