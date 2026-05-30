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
- NFR-004: Package/runtime fields must be pin-ready: the manifest must expose
  where package id, version, checksum, or runtime artifact identifiers will be
  recorded when real Node bundles are provisioned.
- NFR-005: Focused tests must cover positive manifest construction and negative
  hardening denials.
- NFR-006: This first slice must not add host shell escapes or host-only success
  markers as a substitute for guest-side evidence.
