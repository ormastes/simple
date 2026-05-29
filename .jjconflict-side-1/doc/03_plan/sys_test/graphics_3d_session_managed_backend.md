<!-- codex-design -->
# System Test Plan: Graphics 3D Session Managed Backend

Date: 2026-05-17
Status: candidate test plan

## Coverage Matrix

| Requirement | Test area |
|-------------|-----------|
| REQ-GFX-001 | backend capability probe for CPU/CUDA/Vulkan/Metal/WebGPU |
| REQ-GFX-002 | legacy constructors create `LegacyNoSession` |
| REQ-GFX-003 | mode conflict when perf and managed mutable resources mix |
| REQ-GFX-004 | 2D, 2D game, 3D, 3D game, web, GUI, WM accept common policy |
| REQ-GFX-005 | optimization provider facts persist and invalidate by policy hash |
| REQ-GFX-006 | public API exposes Pure Simple and native boundary is C ABI |
| REQ-GFX-007 | ARM/RISC-V 32/64 capability records exist |

## Required Fixtures

- CPU reference renderer for deterministic 2D and 3D mini scenes.
- Fake backend adapter for mode-conflict and device-loss testing.
- Capability fixture for CUDA/Vulkan/Metal/WebGPU without requiring all devices on one host.
- Perf fixture that creates both managed and perf sessions and verifies counter isolation.
- Web/GUI/WM fixture that passes a shared policy object across surfaces without raw backend handles.

## Gates

- No spec may use placeholder assertions such as `expect(true).to_equal(true)`.
- Every `REQ-GFX-*` must have at least one positive and one negative/error-path assertion.
- Perf tests must report whether CPU readback occurred.
- Backend-specific tests must skip cleanly when hardware/API is unavailable, but CPU and fake backend tests must always run.
