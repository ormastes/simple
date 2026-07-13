# SimpleOS QEMU Host-GPU 2D

Status: implementation in progress. The host executor now admits checked
shared-session Vulkan and Metal child surfaces for canonical offset/opacity WM batches;
the wrapper and its fail-closed parser self-test still exercise the shared
full-frame IMAGE Draw IR fixture. Earlier
Linux/Vulkan live x86_64, AArch64, and RV64 raw-render receipts pass; refreshed
cross-ISA Draw IR and CUDA ProcessingIR receipts remain pending. Native Metal
Draw IR execution is implemented but its prepared-macOS receipt remains
unavailable; DirectX remains software emulation and cannot pass.

This scenario proves that supported SimpleOS guests use one bounded protocol to
execute Draw IR and ProcessingIR on a real host device. Unsupported rows retain
the CPU/software fallback and report a stable reason.

## Primary flow

1. **Probe the QEMU guest GPU capability.** Boot the selected x86_64, AArch64,
   or RISC-V guest and negotiate protocol version, limits, backend sets,
   readback, and host readiness.
2. **Render and read back the Simple 2D parity fixture.** Correlate frame ID,
   native device identity, positive backend handle, same-frame output, and the
   exact CPU-oracle checksum.
3. **Submit the canonical full-frame IMAGE composition through the shared guest bridge.**
   Use the same 64x48 opaque background-and-rectangle oracle as one clipped
   full-target `DrawIrComposition` IMAGE resource.
4. **Compare Draw IR readback and correlated device receipt across all three ISAs.**
   Require the exact checksum and pixel counts with positive Vulkan handle and
   device identity before accepting the marker.
5. **Dispatch the raw CLEAR and solid RECT fixture through checked Vulkan commands.**
   Route the existing raw QEMU framebuffer mutations through fenced completion
   evidence.
6. **Reject unchecked or fallback raw rendering before device-backed receipt.**
   Known failure invalidates device provenance; unknown completion poisons the
   frame rather than replaying it.
7. **Select host presentation or the existing local production renderer.**
   The x86 desktop maps the full ivshmem BAR into its active VMM, derives a
   fresh generation only from an idle slot, submits the canonical WM Draw IR,
   validates the correlated device receipt, and presents checksum-checked MMIO
   readback. Any failure falls through to local Engine2D. The current 4K entry
   honestly selects local rendering until TODO 552 expands the bounded wire.
8. **Run the ProcessingIR parity fixture.** Correlate the host completion and
   require exact output-buffer parity with the CPU oracle.
9. **Report device-backed host acceleration evidence.** Publish one row with
   host, guest ISA, QEMU/device arguments, protocol, backend, device, IDs,
   timing, RSS, checksums, status, and reason.
10. **Validate cached rows before aggregation.** Accept a cached passing report
   only when all nine host/ISA rows are present and the three Linux rows link
   to serial logs containing the exact render, Draw IR, and ProcessingIR
   receipts.

## Failure and fallback checks

- Missing service/backend reports `unsupported` or `blocked` and leaves the
  guest bootable on its existing CPU/software path.
- Unknown versions, oversized payloads, invalid dimensions/references,
  duplicate completions, and stale IDs fail before device execution.
- QEMU flags, screenshots, VirtIO-GPU scanout, CPU mirrors, compile-only
  output, missing readback, and synthetic or zero handles cannot pass.

## Platform matrix

Linux uses Vulkan for rendering and CUDA for ProcessingIR on a prepared NVIDIA
host, with Vulkan ProcessingIR retained when CUDA is unavailable. Metal Draw IR
requires a prepared native macOS host and exact device receipt; Metal
ProcessingIR remains unavailable. DirectX cannot pass until a native D3D owner
replaces the current software-emulation backend. Cross-ISA TCG rows
prove correctness and honest provenance; they are exempt from native-ISA
latency and speedup targets.

## Verification

Run the parser contract without hardware:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test
```

Validate a cached wrapper report before another checker consumes it:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --validate-report path/to/report
```

Status-only or incomplete cached reports fail closed as malformed evidence.

Run the live Linux Vulkan-render/CUDA-processing matrix with a deployed
pure-Simple compiler and CUDA+Vulkan runtime artifact:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

The default path builds guests through the named `_QemuRunner` scenarios.
`SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS=1` is an explicit cached-artifact
evidence mode; it is not a fresh-build claim.

## Executable source

`test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`
