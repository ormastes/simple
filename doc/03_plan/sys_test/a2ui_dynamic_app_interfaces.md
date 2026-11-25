# System Test Plan: A2UI and Dynamic App Interfaces

**Feature:** `a2ui_dynamic_app_interfaces`  
**Specs:**
- Unit Core: `test/01_unit/lib/common/ui/a2ui/a2ui_core_spec.spl`
- Unit Authority/Query/HotSwap: `test/01_unit/lib/common/app_interface/app_interface_authority_query_spec.spl`
- Integration (Caret + ClockApp): `test/02_integration/app/a2ui_caret_and_clock_spec.spl`
- System Feature Spec: `test/03_system/app/a2ui/feature/a2ui_dynamic_app_interfaces_spec.spl`
- Native End-to-End Verification Harness: `test/fixtures/a2ui_native_verify.spl` (compiled via pure-Simple Cranelift `native-build`)

## Traceability Matrix

| Requirement | Verification Scope |
| --- | --- |
| REQ-A2UI-001 | G4 import -> strict SDN; shared scalar VM `_` vs `null`; trailing token & `@index()` refusal |
| REQ-A2UI-002 | 8-column flat screen table validation; `order`/`by_key` opaque `c_<hex>` reorder stability |
| REQ-A2UI-003 | Wire JSON v1.0 encoding (`sendDataModel: false`, no table-only fields); bounded JSON byte/token/depth limits |
| REQ-A2UI-004 | Concurrent Caret + ClockApp surfaces with colliding `root`/`refresh`; duplicate `createSurface` refusal; qualified encode/decode |
| REQ-A2UI-005 | `UpdateComponents` complete replacement clearing omitted `variant`; path dependency index |
| REQ-A2UI-006 | `/view` read-only enforcement; `/draft` protected path refusal; foreign principal refusal |
| REQ-A2UI-007 | Restricted SPL query admission; raw SQL & hidden predicate refusal; independent dual-cursor `BoundedChangeJournal` |
| REQ-A2UI-008 | HMAC-SHA256 grants; forged MAC / wrong principal / model_input refusal; `ApprovalBroker`, `PrivilegeStore`, `PrivilegeService` hardening |
| REQ-A2UI-009 | Caret `-1` vs `0` metrics; ANSI sanitization; denied pane hiding; `caret.send` Message-only, stale generation, deduplication/conflict, slash data, `Unknown` |
| REQ-A2UI-010 | Dynamic composition read-only -> interactive preserving `/draft/body`; region escalation (`composer` under `detail`) refusal |
| REQ-A2UI-011 | `CaretA2uiHost.hot_swap_handler` with `aspect_dynload_lifecycle_v1`, async suspend/resume, ABI mismatch refusal, stale surface refusal, quiescence reclaim |
| REQ-A2UI-012 | `ClockApp` ECS stopwatch/timer projection via `clock_mount_a2ui_surface` with zero Caret imports |
