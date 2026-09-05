# SOSIX parallel QEMU and asynchronous host-interface domain research

**Date:** 2026-08-11

## Scope

This companion records the external-system conclusions used by the SOSIX
parallel-QEMU refactor. Repository-specific findings remain in
`doc/01_research/local/sosix_gpu_api_extension_final_report.md` and
`doc/01_research/local/sosix_wm_renderer_host_interface.md`.

## Findings

### GPU-to-OS requests require an asynchronous contract

GPUfs and GPUnet demonstrate that GPU programs can use file and network-like
services through CPU/GPU cooperation. BaM and GeminiFS show why fine-grained
storage traffic needs bounded queues, batching, caching, and coalescing rather
than one blocking host call per GPU lane. SOSIX should therefore expose
submission and completion operations, not pretend CUDA device code has normal
blocking POSIX semantics.

### Initiation, control, and data paths are distinct

CUDA system-scope synchronization can support a CPU/GPU submission ring when
the selected memory type and device capabilities are proven at runtime.
GPUDirect Storage can avoid a CPU bounce copy, while current cuFile calls still
originate on the CPU. A device-originated SOSIX request may consequently use a
host control plane and a direct device data path without semantic conflict.

### Host rendering belongs behind capabilities

Window creation, input production, presentation, timing, and platform event
loops differ across Windows, Linux, macOS, BSD, and SimpleOS. Rendering
semantics should remain above that boundary: GUI and web producers emit the
canonical composition representation, while SOSIX owns asynchronous host
surface, input-stream, deadline, and completion capabilities. This avoids
embedding SDL, Win32, Cocoa, X11/Wayland, or device-driver assumptions in the
renderer.

### Cross-host QEMU evidence cannot be relabelled

KVM, WHPX, HVF, and TCG are host-specific execution capabilities. A Linux TCG
run is useful cross-architecture evidence but is not Windows, macOS, or
FreeBSD-host evidence. Each matrix row therefore needs actual-host admission,
the exact accelerator and QEMU command, source/compiler/media identities, and
a retained boot/mount/list/program transcript. Unsupported or postponed rows
must remain explicit non-PASS evidence with an owner and resume command.

## Applied requirements

- One configured storage owner: `/mnt/data/.simple` on this host and
  `~/.simple` by default elsewhere.
- Six guest identities: x86_32, x86_64, arm32, arm64, riscv32, riscv64.
- Four actual host identities: Linux, Windows, macOS, FreeBSD.
- Parallel execution uses isolated artifacts and deterministic wait-all
  aggregation.
- Guest success proves boot, real filesystem mount, real directory listing,
  target-native program load, observable program output, and exit status.
- SOSIX host and GPU APIs are bounded and asynchronous; synchronous POSIX is a
  compatibility adapter over typed completion waiting.

## Primary source basis

- NVIDIA CUDA Programming Guide: memory model, system thread scope, and CUDA
  graph restrictions.
- NVIDIA GPUDirect Storage cuFile API Reference.
- GPUfs: *Integrating a File System with GPUs*, ASPLOS 2013.
- GPUnet: *Networking Abstractions for GPU Programs*, OSDI 2014.
- BaM: *GPU-Initiated On-Demand High-Throughput Storage Access*, ASPLOS 2023.
- GeminiFS: *A Companion File System for GPUs*, FAST 2025.
- NVIDIA NVSHMEM documentation for kernel-initiated communication.
- QEMU accelerator documentation for KVM, WHPX, HVF, and TCG selection.

## Limitations

This document records the conclusions already established by the final SOSIX-G
audit. Native Windows, macOS, and FreeBSD executions are deployment evidence,
not facts that can be inferred from a Linux-hosted QEMU run.
## 2026-08-12 evidence interpretation update (append-only)

Cross-architecture emulation success and release provenance are separate
claims. A guest transcript can truthfully establish device-visible media,
filesystem traversal, and program execution while remaining inadmissible for a
release matrix because source cleanliness, compiler identity, firmware hash,
or native-host identity is absent. Accordingly, the 24-cell matrix must keep
diagnostic facts in retained artifacts while reporting every unadmitted cell as
non-PASS. A target-side directory enumeration must derive names from directory
records, not from a compiled expected-name table.

The immutable collector snapshot on 2026-08-12 is **0 PASS / 24**. Narrow
Linux diagnostic success does not alter that release-admission count.
