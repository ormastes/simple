<!-- codex-design -->
# Architecture: SimpleOS I/O, Audio, and GPU Audio Offload

## Decision

Use MDSOC virtual capsules around six stable pure-Simple interfaces: `SimpleEventDevice`, `SimpleIoDevice`, `SimpleAudioDevice`, `SimpleAudioGraph`, `SimpleSpatialAudio`, and `SimpleAudioOffloadDevice`. Platform and guest adapters are leaf capsules; graph semantics, event ordering, clocks, resource ownership, and CPU reference behavior remain common.

| Layer | Owners | Responsibility |
|---|---|---|
| Contracts | `src/lib/common/io/`, `src/lib/common/engine/audio/` | Typed capabilities, formats, events, immutable work, errors, receipts |
| Graph | `src/lib/nogc_async_mut/audio_graph/` | Direct/2D/3D commands, buses, effects, spatial lowering, CPU render |
| Offload | `src/lib/nogc_async_mut/audio_offload/` | Prewarmed plans, bounded scheduling, parity/fallback telemetry |
| Desktop | `src/lib/nogc_async_mut/io/audio_backend_*/` | PipeWire/ALSA, CoreAudio, WASAPI, sndio/OSS capsules |
| Hosted events | `src/lib/nogc_sync_mut/io/simple_{glfw,sdl3}.spl` | GLFW and SDL3 lower native events into the same bounded `WindowEventLoop`; neither aliases or falls back to the other |
| SimpleOS service | `src/os/services/{input,audio}/` | Exclusive device ownership, bounded IPC/shared PCM, event publication |
| Guest drivers | `src/os/drivers/virtio/`, `src/os/drivers/audio/` | VirtIO input/sound, retained HDA, DMA/IRQ/ring lifecycle |
| Evidence | `test/`, `scripts/check/` | Native/QEMU provenance, PCM/event hashes, NFR/resource receipts |

## Capsule rules

Platform capsules implement contracts and cannot import Engine2D/3D. Scene adapters only emit graph commands. Offload cannot own device callbacks or final output. CPU rendering is always available and defines semantics. Existing sound-engine, HDA, event route, and spatial modules are migrated behind adapters rather than duplicated.

SDL3 is dynamically loaded as SDL3 on Linux, macOS/BSD, and Windows and uses SDL3's nanosecond event ABI and 0x300/0x400 keyboard/mouse ranges. Missing SDL3 is an explicit unavailable result; the SDL2 backend is not a compatibility substitute. GLFW follows the same fail-closed rule and both adapters publish through the canonical bounded scalar event owner.

## Lifecycle and ownership

Device state is `Closed → Open → Negotiated → Running → Draining → Closed`, with `Lost` reachable from live states. DMA/period state is `Free → Prepared → Device → Completed → Free`. Every transition returns a generation-bound receipt; stale, duplicate, malformed, or out-of-order transitions fail closed. Shutdown rejects new work, bounds cancellation/drain, masks IRQ, resets queues, unmaps memory, releases handles, then emits one ordered shutdown event.

## Hot-path invariants

Callbacks and IRQ handlers perform no allocation, discovery, environment read, subprocess, shader compilation, unbounded scan, or unbounded lock. They consume preallocated bounded rings. Event sequence and device-clock timestamps are monotonic per device. CPU fallback for each offloaded period is ready before the 60%-period deadline.

QEMU render/GPU and audio transports are separate capsules even though both use
`ivshmem-plain`. The render wire owns matching-device ordinal `0`; the audio
wire owns ordinal `1`. Each mapper programs and returns its own BAR2 window.
Neither capsule may use a generic first-match mapper or reuse the other wire's
base address because their headers, payload ownership, and lifecycle differ.

<!-- sdn-diagram:id=simpleos_io_audio_gpu_offload.architecture -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simpleos_io_audio_gpu_offload.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR
DirectAPI -> SimpleAudioGraph
Engine2D -> SimpleSpatialAudio
Engine3D -> SimpleSpatialAudio
SimpleSpatialAudio -> SimpleAudioGraph
SimpleAudioGraph -> CPUReference
SimpleAudioGraph -> SimpleAudioOffloadDevice
SimpleAudioOffloadDevice -> CPUReference
CPUReference -> SimpleAudioDevice
SimpleAudioDevice -> DesktopCapsules
SimpleAudioDevice -> SimpleOSAudioService
SimpleOSAudioService -> VirtioSound
SimpleOSAudioService -> HDA
InputDrivers -> SimpleEventDevice
SimpleAudioDevice -> SimpleEventDevice
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simpleos_io_audio_gpu_offload.architecture hash=sha256:auto
Direct / Engine2D / Engine3D -> shared graph -> CPU + optional offload -> device
Input + audio lifecycle -------------------------------------------> event ring
```

</details>
<!-- sdn-diagram:end -->

## Architecture risks

GPU queue scheduling may not meet audio deadlines, so offload remains optional and coarse. Native OS ABIs require minimal audited shims but no vendor audio engine. Cross-host environmental evidence remains active until executed natively. The current Rust-seed deployment cannot qualify production evidence.
