<!-- codex-requirements -->
# NFR Requirements: SimpleOS AI CLI JS/Node Port

## Selected Gate

NFR Option 1 with reproducibility pieces from Option 3: security-first,
fail-closed manifests plus deterministic package/QEMU evidence.

## Requirements

- NFR-001: Manifest evaluation must be fail-closed. Missing grants deny file,
  process, network, credential, or terminal authority by default.
- NFR-002: Built-in Codex, Claude, and Gemini smoke manifests must be
  deterministic and free of live authentication requirements.
- NFR-003: QEMU marker expectations must be declared in data, not embedded as
  ad hoc string checks in tests.
- NFR-004: Package/runtime fields must be concrete for staged smoke packages:
  use `0.1.0-smoke.20260530`, `manifest-package-smoke:<app>:20260530`, and
  `simple-js-agent-smoke-stub@20260530` until a real Node bundle replaces them.
- NFR-005: Focused tests must cover positive manifest construction and negative
  hardening denials.
- NFR-006: This first slice must not add host shell escapes or host-only success
  markers as a substitute for guest-side evidence.
- NFR-007: When the full Node.js/V8/libuv artifact is unavailable, serial
  evidence must report blocker id
  `blocked:no-full-node-v8-libuv-artifact-20260530` rather than a generic
  pending status.
