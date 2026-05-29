<!-- codex-research -->
# Shared WM Renderer Unification — NFR Requirements

Date: 2026-05-29
Selected NFR path: WM production gate.

## NFRs

NFR-001: API parity

The shared web render API and Engine2D API must be source-level contracts with conformance tests. Passing tests must prove the relevant adapters use the shared contracts, not merely duplicate method names.

NFR-002: Runtime parity

Representative fixtures must exercise equivalent web-render requests and equivalent 2D draw requests across available backends. Hardware-specific backends may report unavailable capability, but must not silently fall back while claiming the unavailable backend rendered the frame.

NFR-003: WM parity

Host and SimpleOS WM paths must share service/core logic for the common lifecycle operations. Adapter-only divergence is allowed for platform display, input source, and native host window effects.

NFR-004: Memory

The GUI/web render refactor must reduce or avoid duplicated render buffers and hot-path string/pixel copies where practical. The design must document buffer ownership, readback ownership, and invalidation.

NFR-005: Size comparison

The Qt baseline and Simple GUI/web-render artifact sizes must be reported in a reproducible format. The comparison must include command, artifact path, byte size, and availability status.

NFR-006: Performance evidence

Verification must include warm startup or initialization timing for the GUI/web-render path, representative render request latency, and max RSS or documented local equivalent when available.

NFR-007: Dirty worktree safety

Implementation must not revert unrelated modified files. Changes must stay scoped to the renderer, Engine2D, WM, tests, and documentation required by this feature.

NFR-008: Release gate

Before release, the verify report must show `STATUS: PASS`. If shared `src/lib/**` changes affect compiler/core or tooling surfaces, run the required core/lib/MCP smoke checks from `AGENTS.md`.
