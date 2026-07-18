<!-- codex-design -->
# Showcase apps architecture

`showcase_catalog` is the identity and metadata owner. It exposes three entries and maps each entry to a render/state module plus standalone, host-WM, and SimpleOS-WM adapters.

Application modules own deterministic state, rendering, hit testing, and semantic snapshots. Surface adapters own only window creation, WM/IPC transport, event conversion, presentation, and evidence capture. The host adapter may use the existing filesystem bridge; the SimpleOS adapter must use installed-app identity and OS WM/IPC/shared-framebuffer facilities.

The browser application loads the canonical standards page through BrowserApp. Placeholder renderers must return explicit unsupported diagnostics and are excluded from successful surface evidence. Engine2D evidence includes backend handle/provenance and same-frame device readback where the backend supports it.

Catalog IDs are stable across surfaces; installed paths are mappings, not new logical identities. This prevents launcher, WM scene, docs, and tests from drifting into separate app definitions.
