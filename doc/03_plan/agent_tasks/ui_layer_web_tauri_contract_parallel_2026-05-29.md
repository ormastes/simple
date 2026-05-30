# UI Layer Web/Tauri Contract Parallel Lane - 2026-05-29

Scope owned by this lane:
- `test/unit/app/ui/ui_layer_web_tauri_contract_spec.spl`
- `doc/03_plan/agent_tasks/ui_layer_web_tauri_contract_parallel_2026-05-29.md`

Goal:
- Prove the 2D UI layer can feed both the Simple web rendering layer and the Tauri web rendering layer through the same request/artifact/capability contract.

Contract checked:
- A single UI tree is rendered once through `render_html_tree`.
- `WebBackend.render_html` and `TauriBackend.render_html` both consume that same body HTML.
- `WebBackend.generate_full_page` equals `web_render_to_artifact(WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, ...)).html`.
- `TauriBackend.generate_full_page` equals `web_render_to_artifact(WebRenderRequest.html(WEB_RENDER_TARGET_TAURI, ...)).html`.
- `tauri_render_ipc_json` equals the Tauri artifact IPC JSON.
- Backend capabilities match `web_render_capabilities_for_target` for mouse/touch, and artifact capability summaries match `web_render_capability_summary`.

Commands/results:
- `bin/simple test test/unit/app/ui/ui_layer_web_tauri_contract_spec.spl --mode=interpreter`
  - PASS: 1 file, 1 passed, 0 failed, 696 ms.

Scoped diffs/fixes:
- No contract diff was found.
- No production code fix was required.

Remaining blockers:
- None in this scoped lane.
