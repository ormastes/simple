# GPU Renderer Processing Backends Requirements

These requirements restate the user-selected scope captured by
`.spipe/gpu_renderer_processing_backends/state.md`; no optional requirement is
selected implicitly.

- REQ-001 (AC-1): One shared `ProcessingIr` and backend artifact/evidence
  contract serves Vulkan, CUDA, Metal, DirectX translation, and CPU oracle use.
- REQ-002 (AC-2): A representative web/Engine2D drawing kernel compiles to
  validator-accepted SPIR-V, executes on physical Vulkan, and exactly matches
  device-origin readback to the CPU oracle.
- REQ-003 (AC-3): CUDA generation emits real PTX, compiles through the canonical
  source-matched probe, and native CUDA device readback exactly matches the CPU
  oracle when an admitted pure-Simple compiler is available.
- REQ-004 (AC-4): Validated ProcessingIR deterministically generates Metal MSL
  after research and architecture/design are recorded.
- REQ-005 (AC-5): macOS Metal compiles and executes the exact validated MSL
  artifact and compares raw device readback to the CPU oracle; unavailable-host
  evidence remains blocked with an exact resume contract.
- REQ-006 (AC-6): Invalid artifacts, compiler/validator failure, unavailable
  devices, unsupported operations, and CPU mirrors fail closed without GPU PASS.
- REQ-007 (AC-7): Unit, integration, and SSpec coverage proves generation,
  validation, selection, submission, provenance, parity, and invalidation.
- REQ-008 (AC-8): Architecture, backend guide, test plan, and generated manuals
  describe hot paths, cache/invalidation, backend order, budgets, and native
  evidence commands.
- REQ-009 (AC-9): Focused checks, direct-runtime guards, stub scans, and generated
  spec layout gates pass before verification.
- REQ-010 (AC-10): Parallel lane results preserve unrelated work and receive
  final high-capability traceability and manual-quality review.
- REQ-011 (AC-11): Drawing access preserves bindings, stride, coordinates, pixel
  semantics, and oracle results through CUDA-to-Vulkan, CUDA-to-DirectX,
  Vulkan-to-Vulkan, and Metal-to-Metal paths.
- REQ-012 (AC-12): DirectX generation has host-independent HLSL/binding tests and
  an executable Windows raw-device-readback resume contract that cannot pass on
  an unavailable host.
- REQ-013 (AC-13): Environment evidence identifies the loaded runtime library,
  canonical HAL/wrapper owner, compiler/validator, physical device or emulator,
  memory capabilities, and readiness reason without promoting presence to PASS.
- REQ-014 (AC-14): Physical Vulkan and CUDA scenarios prove CPU upload, GPU
  dispatch, GPU download, repeated reuse, positive/stable identity and handle,
  exact byte/pixel parity, and invalid-transfer rejection through the canonical
  HAL/wrapper path.
- REQ-015 (AC-15): Metal emulation proves artifact, bindings, dispatch,
  framebuffer/readback, and failure state transitions without claiming hardware;
  the same semantic scenario remains executable as native Metal on macOS.
