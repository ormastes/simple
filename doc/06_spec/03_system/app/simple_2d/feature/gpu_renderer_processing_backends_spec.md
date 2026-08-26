# GPU Renderer ProcessingIR Vulkan Backend

This scenario proves that the shared `ProcessingIR` drawing contract reaches a
validated SPIR-V binary and native Vulkan device readback. A CPU mirror is used
only as the oracle; it cannot satisfy the device-origin gate.

Traceability: REQ-001/REQ-002 cover the shared contract and physical Vulkan
execution, REQ-011 covers drawing semantics, REQ-006/REQ-007 cover fail-closed
evidence and scenario quality, and REQ-008/REQ-010 cover architecture freshness
and cooperative integration. Each mapped requirement group has independent
happy, edge, and error scenarios in the executable system spec.

## Contract edge and error flows

- The smallest valid one-pixel rectangle preserves half-open coordinates and
  stride in its semantic key.
- An out-of-bounds rectangle is rejected before device submission.
- A complete immutable artifact validates; changing IR semantics invalidates
  it; an empty payload cannot report submission or device origin.
- Architecture, operator commands, merge ownership, and generated-manual review
  are executable documentation assertions rather than release-time assumptions.

## Coverage evidence

Focused unit scenarios exercise successful source/binary artifacts, drawing
extent and size boundaries, and invalid/missing artifact states. Measurement is
requested with `--coverage`; current tooling produces no branch counters, so the
retained report records `branches_total=unavailable`,
`branches_hit=unavailable`, and `branch_coverage_percent=unavailable`. Scenario
count is explicitly not treated as coverage. Resume after the tracked
instrumentation bug is fixed using the exact command in
`build/test-artifacts/coverage/gpu_renderer_processing_backends/branch_coverage.receipt`.

## Validated FillRect flow

1. **Select representative renderer processing kernels** — construct a 16×16,
   row-major `FillRectU32` operation with explicit stride and half-open bounds.
2. **Lower shared ProcessingIR for the selected backend** — request
   `ProcessingBackendTarget.VulkanSpirv` and require a non-empty binary artifact.
3. **Translate drawing access for the destination backend** — bind coordinate,
   extent, stride, and pixel semantics into the artifact semantic key so a
   coordinate change invalidates cached material.
4. **Compile and validate the backend artifact** — write the exact retained
   binary and run `spirv-val --target-env vulkan1.1`.
5. **Submit native work and capture device readback** — dispatch the Vulkan
   filled-rectangle kernel and require `device_readback`, a positive backend
   handle, no CPU fallback, and known completion.
6. **Compare device readback with the CPU oracle** — compare every raw `u32`
   pixel against the shared ProcessingIR oracle.

Run on a prepared Linux Vulkan host:

```text
bin/simple test test/03_system/app/simple_2d/feature/gpu_renderer_processing_backends_spec.spl --mode=interpreter
```

Missing `spirv-val`, Vulkan initialization, a physical device, submission, or
device readback is a failure. The scenario does not replace those rows with a
CPU pass.

## Compiler-produced drawing qualification

`test/02_integration/rendering/vulkan_compiler_fill_rect_live_spec.spl`
independently lowers a representative 6×5 rectangle through frontend, HIR,
MIR, and the Vulkan backend. Because the current Vulkan ABI admits one scalar
push constant, the fixed rectangle offsets and five row stores are compiled
into the kernel while its width remains the runtime bound. The resulting
assembly is assembled and validated for Vulkan 1.3, then executed against a
zeroed 16×16 storage buffer. Passing evidence includes a discrete/integrated
device identity, 1024 device-read bytes, and mismatch count zero.
It retains assembly, SPIR-V, artifact SHA-256, compiler/assembler/validator
identity, device/driver identity, byte count, and mismatch count under
`build/test-artifacts/02_integration/rendering/vulkan_compiler_fill_rect_live/`.

## Focused production web route

Use the bounded production producer gate when the broad web parity suite is too
slow for a focused backend qualification:

```text
bin/simple run test/02_integration/rendering/web_vulkan_production_readback_spec.spl
```

This is not a synthetic Engine2D-only scene. It sends HTML and CSS through the
production layout presenter, canonical DrawIR, and Engine2D. It renders the
same document once through the CPU oracle and once through strict Vulkan, then
requires a positive backend handle and device identity, `device_readback`, no
degraded render, equal raw pixels, and equal checksums. The render-budget floor
only disables diagnostic budget degradation; it does not bypass layout,
painting, submission, synchronization, or readback.
The machine-readable production receipt is retained at
`build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/production_web_vulkan.receipt`
with command, evidence class, producer/backend identity, handle/device identity,
pixel count, CPU/GPU checksums, mismatch count, and parity status.

The same physical run retains the GPU-read image at
`build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/production_web_vulkan.ppm`
and an ordered producer-to-readback event trace at
`build/test-artifacts/02_integration/rendering/web_vulkan_production_readback/production_web_vulkan.events.jsonl`.
The trace records the producer, DrawIR, Engine2D, Vulkan dispatch handle/device,
and device-readback checksum as distinct ordered events.
