# Simple WM Host and SimpleOS Fullscreen Requirements

**Selection:** Feature Option A, selected 2026-07-11.

- **REQ-1:** The production host WM shall enter windowed mode, toggle to native borderless fullscreen, and restore prior host geometry while preserving internal window IDs, geometry, focus, z-order, minimized state, and taskbar state.
- **REQ-2:** SimpleOS shall present a full framebuffer desktop at detected scanout dimensions; internal maximize/restore shall be triggered by real input and preserve live compositor state.
- **REQ-3:** Host and SimpleOS shall render multiple real `SharedWmScene` internal windows plus shared taskbar and top title/command lane through production object models.
- **REQ-4:** Outer chrome shall use the backend-neutral Simple 2D executor and app content canonical Simple GUI/Simple Web artifacts; arbitrary titles/content shall replace canned templates and text allowlists.
- **REQ-5:** Production entrypoints shall not use Rust-seed execution, fixed demo HTML, hardcoded pixel scenes, fixed QEMU replies, synthetic taskbar surfaces, or boot-time choreography as completion evidence.
- **REQ-6:** Pointer/keyboard input shall cover focus, drag, minimize, taskbar restore, internal maximize/restore, host fullscreen entry, and host fullscreen exit with correlated state revisions.
- **REQ-7:** Evidence shall record executable/entrypoint/backend provenance, input sequence, before/after state, viewport/scanout metadata, semantic pixels, frame hashes, and verified captures; missing/unverifiable evidence fails closed.
- **REQ-8:** SPipe scenarios shall exercise production entrypoints with no placeholder passes, source-only success claims, masked failures, or demo-only markers; mirrored manuals shall describe the operator flow.

Physical-board evidence is excluded; QEMU is the required SimpleOS runtime environment.

