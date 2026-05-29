<!-- codex-research -->

# HTML/CSS Binary Caching Requirements

Selected scope: first milestone from the prior plan, combining a shared-boundary binary/static cache identity with containment/dynamic-island metadata and GTK comparison evidence.

- REQ-HCBC-001: The shared web render API shall expose deterministic cache identity metadata for HTML/CSS/Simple UI render requests.
- REQ-HCBC-002: The cache identity shall include target, surface, viewport, pixel-output mode, capability summary, title, body HTML, CSS, JS, and cache schema version.
- REQ-HCBC-003: The API shall classify a request as a fully cacheable static shell or a static shell with dynamic islands.
- REQ-HCBC-004: Dynamic island detection shall recognize `data-simple-dynamic`, `data-live`, `data-ui-patch`, and WebSocket-backed JS as invalidating dynamic markers.
- REQ-HCBC-005: Electron and Tauri artifact generation shall avoid rebuilding full HTML for IPC after full HTML has already been built for the artifact.
- REQ-HCBC-006: The repo shall provide a GTK comparison harness that records Simple render-loop speed and GTK minimal GUI size/speed when GTK tooling is available.
- REQ-HCBC-007: GTK comparison shall degrade to an explicit unavailable status instead of failing on hosts without GTK or display access.
- REQ-HCBC-008: Static-shell HTML artifacts shall be persistable by cache key for reuse across render requests.
- REQ-HCBC-009: Repeated static-shell requests shall use an in-memory hot cache before touching persistent storage.
- REQ-HCBC-010: Dynamic island requests shall not be persisted as fully static shell artifacts.
- REQ-HCBC-011: Static-shell requests shall expose a compact binary-plan artifact that records cache key, viewport, source byte counts, dynamic count, command count, and render plan.
- REQ-HCBC-012: The GTK comparison report shall include static-shell size evidence for generated full HTML, compact Simple static-shell plan, and GTK minimal executable.

Out of scope for this milestone: full binary encoded DOM/style/layout payloads, GPU backend parity, shader binary generation, and full retained scene graph invalidation.
