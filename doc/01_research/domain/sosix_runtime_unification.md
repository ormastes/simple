<!-- codex-research -->
# SOSIX runtime unification: domain constraints

**Reviewed:** 2026-09-26. Sources below are primary specifications, official project documentation, or maintainer manual pages. These constraints inform requirement choices; none proves this repository's implementation.

| Constraint | Primary evidence | Requirement consequence |
|---|---|---|
| Positioned I/O and append | [POSIX `write`/`pwrite`](https://pubs.opengroup.org/onlinepubs/9699919799/functions/write.html) specifies an explicit write position even with `O_APPEND`; [Linux `pread`/`pwrite` manual](https://man7.org/linux/man-pages/man2/pwrite64.2.html) documents that Linux appends with `O_APPEND` despite the supplied offset. | A native raw alias and an unqualified cross-platform POSIX-exact `pwrite` promise cannot both be claimed for arbitrary Linux descriptors. Specify a raw-native contract, a checked strict route, or a qualified descriptor precondition. |
| Cancellation versus retirement | [liburing cancellation documentation](https://man7.org/linux/man-pages/man7/io_uring_cancelation.7.html) and [cancel-by-fd API](https://man7.org/linux/man-pages/man3/io_uring_prep_cancel_fd.3.html) distinguish a cancellation request/result from the target request's completion. | A timeout or cancel acknowledgment cannot by itself release a buffer, operation slot, or provider generation. Require target completion or a provider-specific proven retirement signal. |
| Registered-buffer lifetime | [Linux `io_uring_register(2)`](https://man7.org/linux/man-pages/man2/io_uring_register.2.html) describes registered buffers and their pinned-memory behavior. | Bound registration counts/bytes and retain leases through quiescence; a logical close is insufficient release evidence. |
| GPU memory visibility | [Vulkan synchronization specification](https://docs.vulkan.org/spec/latest/chapters/synchronization.html) separates execution dependencies from memory availability/visibility; [CUDA memory model](https://docs.nvidia.com/cuda/cuda-programming-guide/05-appendices/cuda-cpp-memory-model.html) qualifies system-scope atomics by device and memory type. | Do not infer a universal live CPU/GPU shared ring. Qualify each transport, memory allocation, barrier and device/profile combination. |
| Proxy versus direct storage | [NVIDIA GPUDirect Storage overview](https://docs.nvidia.com/gpudirect-storage/overview-guide/) describes CPU-issued cuFile APIs even when DMA avoids CPU memory. | Zero-copy data movement alone does not prove GPU-initiated direct queue authority. Keep host-proxy and direct-device receipts distinct. |
| Driver conformance | [Khronos Vulkan CTS guide](https://github.khronos.org/Vulkan-Site/guide/latest/vulkan_cts.html) identifies implementation/driver conformance testing. | CTS version is useful provider metadata; SOSIX still needs its own end-to-end request, completion, buffer-lifetime, reset and rendering evidence on each named profile. This is an inference from the CTS scope. |

## Decisions that cannot be inferred from sources

1. Whether the raw `pwrite` projection promises native host behavior or normative POSIX behavior on Linux `O_APPEND` descriptors.
2. Whether cancellation returns a logical result early with a separate retirement handle, or waits for physical retirement. Both must preserve leases; the release latency differs.
3. Which exact native hosts, QEMU guests, GPU backends, physical boards, drivers and memory types block each release boundary. A software or emulator pass cannot stand in for an untested native row.

The existing 2026-09-05 SOSIX proposal already incorporates much of this domain work. This note isolates the decisions that still need an explicit selected contract and current evidence.
