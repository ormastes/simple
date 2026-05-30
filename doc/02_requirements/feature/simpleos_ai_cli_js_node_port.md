<!-- codex-requirements -->
# Feature Requirements: SimpleOS AI CLI JS/Node Port

## Selected Path

Feature Option A: contract-first compatibility layer.

The first complete implementation step is a SimpleOS AI CLI manifest contract
that defines the Node-compatible OS surface required by Codex, Claude, and
Gemini CLI workflows, maps those needs to explicit SimpleOS capability grants,
and provides QEMU marker expectations before a full Node/V8/libuv port lands.

## Requirements

- REQ-001: Define a manifest model for AI CLI apps with app id, runtime kind,
  executable path, terminal requirement, file grants, process grants, network
  grants, credential grants, and QEMU marker fragments.
- REQ-002: Provide built-in manifest constructors for Codex, Claude, and Gemini
  CLI smoke workflows.
- REQ-003: Convert each manifest to a deterministic capability summary covering
  file, process, network, credential, terminal, and QEMU marker requirements.
- REQ-004: Reject manifests that omit required identity/runtime/entry fields or
  request unsupported runtime kinds.
- REQ-005: Treat child-process spawning, network access, and credential access
  as denied unless the manifest declares the matching grant.
- REQ-006: Preserve the current interpretation of `x85` as x86 for target
  planning unless the user corrects it.
- REQ-007: Record the full Node.js/V8/libuv port as a later implementation
  layer, not a prerequisite for this first manifest-hardening slice.
- REQ-008: Define a Bun-informed Simple JS runtime profile that keeps Bun-like
  single-tool cohesion for runtime, package, transpile, bundle, and test
  surfaces while preserving the Simple MDSOC+ architecture boundary.
- REQ-009: Define the WebAssembly/browser integration contract for generated GUI
  WASM, including supported host targets, allowed imports, denied host escapes,
  required exports, and browser-render evidence markers.
- REQ-010: Materialize deterministic SimpleOS staged smoke package contents for
  each AI CLI manifest, including manifest SDN, launcher source, runtime stub
  source, package index, marker payload, and fail-closed source hardening checks.

## Acceptance Mapping

- AC-1: REQ-001, REQ-003, REQ-007.
- AC-2: REQ-003, REQ-004, REQ-005.
- AC-3: REQ-001, REQ-002.
- AC-4: REQ-001, REQ-003, REQ-010.
- AC-5: REQ-005, REQ-010.
- AC-6: REQ-001 through REQ-005, REQ-008, REQ-009, REQ-010.
- AC-7: REQ-007.
