<!-- codex-research -->
# Shared WM Renderer Unification — Feature Requirements

Date: 2026-05-29
Selected path: full WM and renderer stack unification.

## Scope

Make the GUI layer access web rendering through a common API, refactor pure Simple web rendering into that API, make CUDA 2D share the CPU/Metal Engine2D API, and refactor host WM and SimpleOS WM so most window-management logic is shared.

## Requirements

REQ-001: Shared web render API

The repo must expose one Simple-owned web render API used by `ui.web`, `ui.electron`, `ui.tauri`, and the pure Simple browser/web renderer path. The current canonical file is `src/lib/common/ui/web_render_api.spl`, consumed by `src/app/ui.web/backend.spl`, `src/app/ui.electron/backend.spl`, `src/app/ui.tauri/backend.spl`, and the pure Simple browser path covered by `test/unit/app/ui/web_render_backend_api_spec.spl`. The API must cover at minimum:

- render request metadata
- HTML/body rendering
- snapshot or patch rendering hooks
- input forwarding hooks
- capability reporting
- host window command serialization
- optional pixel output for pure Simple rendering

REQ-002: GUI layer uses shared web API

GUI backends must call the shared web render API instead of duplicating web-render request construction. Electron and Tauri may keep platform IPC adapters, but the render payload and capability decisions must come from the common API.

REQ-003: Pure Simple web renderer participates

The pure Simple web renderer must expose or consume the same API shape as the host web adapters. Pixel/framebuffer output may be an optional capability, but it must be represented in the shared API rather than hidden behind an unrelated path.

REQ-004: Engine2D backend API convergence

`std.gpu.engine2d.backend.RenderBackend` in `src/lib/gc_async_mut/gpu/engine2d/backend.spl` is the canonical 2D renderer API. CPU, Metal, and CUDA 2D backends in `backend_cpu.spl`, `backend_metal.spl`, and `backend_cuda.spl` must implement that same interface or explicitly report unavailable capability through a typed backend result without pretending success.

REQ-005: CUDA 2D backend

The missing CUDA 2D backend module must be added or restored so `Engine2D` backend selection can compile against a CUDA backend that shares the CPU/Metal interface.

REQ-006: Engine2D session API convergence

Session-oriented Engine2D APIs must wrap or delegate to the canonical `RenderBackend` surface rather than creating a competing draw API for CPU/CUDA/Metal.

REQ-007: Shared host and SimpleOS WM logic

Host WM and SimpleOS WM must share core window lifecycle and routing logic for create, focus, move, resize, minimize, restore, close, and input routing. Host-specific and SimpleOS-specific code may remain as adapters below the shared service/core boundary.

REQ-008: Remove duplicate host WM service authority

The host WM path must not define a separate authoritative `WmService` that duplicates or contradicts the real WM service/core. Any local host handle must be a lifecycle adapter around shared WM state.

REQ-009: Shared render APIs in WM paths

Host WM and SimpleOS WM rendering paths must use the shared web render API and the shared 2D engine API where web content or 2D rendering is involved.

REQ-010: Memory optimization during refactor

The refactor must avoid avoidable frame buffer copies, repeated full-frame allocations, repeated JSON/string rebuilds in hot paths, and duplicated render state between GUI layer and web renderer. Any retained buffers must have explicit ownership and invalidation rules.

REQ-011: Qt baseline comparison

Add a reproducible baseline plan or harness for an equivalent Qt-based GUI app and compare binary/package size against the Simple GUI/web-render path. `scripts/check-qt-gui-size-baseline.shs` is the harness. If Qt is unavailable locally, it must record `qt_status=unavailable` as an optional, non-blocking baseline rather than failing normal verification.

REQ-012: Tests and evidence

Add focused tests or specs for:

- shared web render API conformance across Web/Electron/Tauri/pure Simple
- Engine2D backend interface conformance for CPU/Metal/CUDA
- host/SimpleOS WM shared logic parity
- size comparison reporting for the Qt baseline

## Out Of Scope

- Replacing every renderer backend in one patch if a staged API migration is needed.
- Requiring real CUDA hardware in normal CI. CUDA unavailable must be a typed capability state.
- Requiring Qt installation in normal CI.
