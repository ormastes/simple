<!-- codex-design -->
# Agent Plan: Graphics 3D Session Managed Backend

Date: 2026-05-17
Status: candidate implementation plan

## Objective

Extend the 2D backend session-sharing plan into a common graphics session architecture for 2D, 2D game, 3D, 3D game, web renderer, GUI library, and WM. Keep Pure Simple APIs first, use C ABI shims for native GPU calls, avoid adding Rust runtime-library coupling, and share JIT/backend optimization through the optimization plugin system.

## Work Breakdown

1. Common API agent
   - Owns `GraphicsSession`, `GraphicsSessionPolicy`, capability records, mode conflict errors, and old no-session wrappers.
   - Must preserve `LegacyNoSession` behavior.

2. 2D/2D-game adoption agent
   - Maps existing engine2d backend session design to generic `GraphicsSession`.
   - Adds sprite/tile/particle session entry points for 2D game use.

3. 3D/3D-game agent
   - Designs scene resources, render passes, material/bind layout, frame lifecycle, and game-loop integration.
   - Keeps CUDA as compute/interop unless a presentation backend is explicitly configured.

4. Web/GUI/WM agent
   - Routes web renderer, GUI library, and WM through the same session policy.
   - Ensures `UISession` stores UI state only and does not own raw GPU backend handles.

5. Backend adapter agent
   - Implements CPU, Vulkan, CUDA, Metal, and WebGPU adapters behind Pure Simple traits.
   - Uses C ABI shims for native GPU APIs.

6. Optimization/JIT agent
   - Adds graphics optimization providers to the Simple Optimization Plugin registry.
   - Shares provider facts with compiler/JIT/backend lowering.
   - Keeps `ManagedShared` and `PerfExclusive` optimization state separate.

7. Architecture verification agent
   - Adds mode-conflict tests, backend capability tests, CPU golden rendering tests, and perf-counter isolation checks.

## Sequencing

1. Land common types and capability records.
2. Adapt old no-session constructors to call `LegacyNoSession`.
3. Add managed/perf policy checks before backend-specific implementation.
4. Port 2D backend to generic session.
5. Add 3D resource and render-pass skeletons.
6. Integrate web/GUI/WM session policy handoff.
7. Register optimization providers and persistent keys.
8. Add verification and perf comparison fixtures.

## Done Criteria

- All surface families accept a session policy and can still run without one.
- `ManagedShared` and `PerfExclusive` cannot accidentally share mutable resources.
- CPU-only backend passes the same API and spec tests.
- CUDA/Vulkan/Metal/WebGPU adapters report capabilities through one structure.
- Optimization/JIT provider state is persistent and keyed by backend/session policy.
- Docs and specs trace every `REQ-GFX-*` requirement.
