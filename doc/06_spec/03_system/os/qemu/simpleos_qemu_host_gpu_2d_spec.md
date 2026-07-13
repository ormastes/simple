# SimpleOS QEMU Host-GPU 2D

Status: implementation in progress. The canonical wrapper and its fail-closed
parser self-test are implemented. Linux/Vulkan live x86_64, AArch64, and RV64
probes pass rendering plus the ProcessingIR `FillU32` oracle. Native Metal,
DirectX, and CUDA host receipts remain unavailable.

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
3. **Run the ProcessingIR parity fixture.** Correlate the host completion and
   require exact output-buffer parity with the CPU oracle.
4. **Report device-backed host acceleration evidence.** Publish one row with
   host, guest ISA, QEMU/device arguments, protocol, backend, device, IDs,
   timing, RSS, checksums, status, and reason.

## Failure and fallback checks

- Missing service/backend reports `unsupported` or `blocked` and leaves the
  guest bootable on its existing CPU/software path.
- Unknown versions, oversized payloads, invalid dimensions/references,
  duplicate completions, and stale IDs fail before device execution.
- QEMU flags, screenshots, VirtIO-GPU scanout, CPU mirrors, compile-only
  output, missing readback, and synthetic or zero handles cannot pass.

## Platform matrix

Linux Vulkan is the first required live slice. Metal, DirectX/Vulkan, and CUDA
rows run only on prepared hosts. Cross-ISA TCG rows prove correctness and honest
provenance; they are exempt from native-ISA latency and speedup targets.

## Verification

Run the parser contract without hardware:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test
```

Run the live Linux/Vulkan matrix with a deployed pure-Simple compiler and
cached Vulkan runtime artifact:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
```

The default path builds guests through the named `_QemuRunner` scenarios.
`SIMPLEOS_HOST_GPU_USE_EXISTING_GUESTS=1` is an explicit cached-artifact
evidence mode; it is not a fresh-build claim.

## Executable source

`test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`
