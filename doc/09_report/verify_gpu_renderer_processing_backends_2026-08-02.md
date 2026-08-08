# GPU Renderer Processing Backends Verification — 2026-08-02

## Current Linux host

- PASS: CUDA dynamic-driver status normalization regression: 1/1.
- PASS: Physical CUDA HAL upload, two dispatches, readback, and invalid transfer ABI: 3/3; invalid HtoD/DtoH return `-1`.
- PASS: CUDA artifact validation 7/7, drawing translation 5/5, system operator flow 4/4.
- PASS: Metal MSL generation 6/6, emulator 4/4, pipeline 1/1, branch scenarios 3/3.
- PASS: Shared ProcessingIR/Vulkan system flow 9/9 and production Web-to-Vulkan capture 1/1.
- PASS: numbered-artifact, direct-environment, rendering-source-coupling, diff, placeholder, and generated-spec-layout guards.

## Retained visual and event evidence

- Physical Vulkan image: `build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/production_web_vulkan.ppm` (24x20, SHA-256 `b72a4a94e90e96954a4ac2c329b01e7358f86b798a0c9938292bc36e317a2978`).
- PNG viewing derivative: `build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/production_web_vulkan.png`.
- Physical ordered events: `build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/production_web_vulkan.events.jsonl`.
- Metal emulator events: `build/test-artifacts/01_unit/lib/gc_async_mut/processing/metal_emulator/events.log`.

## Release blockers

- FAIL: Native Metal FillU32 and stride-aware FillRect cannot execute on Linux; TODO 652 requires macOS raw-device readback. The Metal system contract correctly reports 1 pass and 2 blocked failures.
- FAIL: Native Windows DirectX remains open under TODO 653.
- FAIL: Measured >=80% source branch coverage is unavailable because the runner lacks compiler-owned decision inventory/outcome attribution.
- FAIL: verification used the freshly rebuilt Rust bootstrap interpreter; a pure-Simple self-hosted final run remains required.

**STATUS: FAIL** — current-host CUDA is repaired and physical execution passes; Metal host-independent/emulator behavior passes, but cross-platform native and release evidence remain incomplete.
