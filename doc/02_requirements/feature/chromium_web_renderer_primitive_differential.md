<!-- codex-research -->
# Chromium primitive oracle library requirements

Selected: Feature Option B — owned native C ABI wrapper over the pinned
Electron broker.

- REQ-CHROME-001: Build `libsimple_chromium_primitive_oracle` as a test-only
  native library exporting exactly the frozen ABI-v1 symbol set.
- REQ-CHROME-002: The library owns a persistent child/session transport to the
  repository-pinned Electron/Chrome broker; it must not spawn per event.
- REQ-CHROME-003: Requests and responses use caller-owned bounded buffers and
  opaque exact-once session handles.
- REQ-CHROME-004: The manifest records ABI, library and broker hashes, Electron
  and Chrome versions, platform/arch, build arguments, and required symbols.
- REQ-CHROME-005: DOM/style/layout/paint/input traces must come from the real
  browser broker and normalize through the canonical trace schema.
- REQ-CHROME-006: CPU `capturePage` is never labeled device-origin GPU
  readback. GPU promotion fails closed until independent device evidence exists.
- REQ-CHROME-007: Missing runtime, timeout, crash, malformed output, ABI/hash
  mismatch, or unsupported primitive returns a typed failure without fallback.
