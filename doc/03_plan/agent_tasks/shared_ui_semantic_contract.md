<!-- codex-design -->
# Shared UI Semantic Contract - Agent Task Plan

Date: 2026-06-03
Status: Candidate plan pending requirement selection

Agents are not alone in the codebase. Each agent owns a disjoint write scope and
must not revert edits outside that scope.

## Agent A: Contract Types

Ownership:
- `src/lib/common/ui/semantic_contract.spl`
- `doc/04_architecture/shared_ui_contract.md`

Tasks:
- Extend the existing protocol version, semantic element/state records,
  commands, dispatch results, snapshots, capabilities, and standard errors.
- Keep this separate from `RenderBackend` and `web_render_api.spl`.

Status:
- Initial `src/lib/common/ui/semantic_contract.spl` facade exists and is covered
  by `test/unit/app/ui/semantic_contract_spec.spl`.
- Semantic command conversion to existing `UIEvent` values and
  `UISession.dispatch_semantic_command(...)` exist for the first S2 event
  dispatch slice.

## Agent B: Adapter State Helpers

Ownership:
- `src/app/ui.tui/backend.spl`
- `src/app/ui.web/backend.spl`
- `src/app/ui.electron/backend.spl`
- `src/app/ui.tauri/backend.spl`
- `src/app/ui.none/backend.spl`

Tasks:
- Add helper functions that produce semantic snapshots for a shared fixture.
- Preserve adapter-private transports.
- Do not require Electron/Tauri/TUI to expose HTTP endpoints.

Status:
- Initial helpers exist in `app.ui.web`, `app.ui.tui`, `app.ui.electron`,
  `app.ui.tauri`, and `app.ui.none`, covered by
  `test/unit/app/ui/semantic_backend_helpers_spec.spl`.

## Agent C: Semantic Event Dispatch

Ownership:
- `src/lib/common/ui/semantic_contract.spl`
- adapter command mapping helpers

Tasks:
- Map click, type, key, focus, resize, drag, submit, and named actions to each
  adapter.
- Return typed dispatch results and read-after-write state evidence.

Status:
- First shared conversion covers click, type, key, action, focus, focus-next,
  focus-prev, and quit. Session dispatch returns read-after-write sequence
  evidence. Resize/drag/submit-specific helpers remain to be filled in.

## Agent D: Renderer Bridge Evidence

Ownership:
- `src/lib/common/ui/web_render_api.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
- relevant renderer/capture tests

Tasks:
- Document and test that web render snapshots are downstream transport/render
  artifacts, not the semantic contract itself.
- Add proof that pure Simple GUI/web can flow from semantic state to web render
  request to Engine2D capture.

## Agent E: System Tests

Ownership:
- `test/system/app/ui/feature/shared_ui_semantic_contract_spec.spl`
- generated/manual mirrored docs under `doc/06_spec/system/app/ui/feature/`

Tasks:
- Prove Web, Native TUI, Electron, Tauri, and headless helpers expose the same
  semantic state for a canonical fixture.
- Prove semantic commands produce equivalent state changes.
- Keep `/api/test` protocol assertions as transport-specific Web/TUI-Web tests.

## Verification

- `find doc/06_spec -name '*_spec.spl' | wc -l` must return `0`.
- SPipe specs must use real assertions, not placeholder passes.
- Missing surface support reports `semantic_adapter_unavailable` rather than a
  transport render pass.
