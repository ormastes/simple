<!-- codex-design -->
# Detail Design: SimpleOS I/O, Audio, and GPU Audio Offload

## Public contracts

`SimpleEventDevice` exposes capabilities/start/stop and writes `SimpleDeviceEvent` into a bounded sink. `SimpleIoDevice` exposes enumerate/open/close. `SimpleAudioDevice` adds negotiate, submit, capture, drain, and cancel. `SimpleAudioGraph` commits immutable command batches and renders epochs. `SimpleSpatialAudio` lowers listener/source records. `SimpleAudioOffloadDevice` negotiates, submits immutable work, and polls bounded status.

| Record | Required fields |
|---|---|
| `AudioFormat` | sample type/rate, channel layout/count, interleave, period frames |
| `AudioPeriod` | generation, sequence, clock range, capacity, valid frames, sample view |
| `SimpleDeviceEvent` | sequence, timestamp, device, generation, kind, status, correlation |
| `AudioCommandBatch` | graph epoch, ordered commands, immutable assets, bounds |
| `ImmutableAudioWork` | kind, epoch, input/output views, kernel pin, deadline, CPU receipt |
| `RenderReceipt` | frames, PCM hash, timings, xruns, backend/offload status, resources |

## Algorithms

The graph drains commands by sequence, renders sources into preallocated buses, applies gain/pan/distance/cone/doppler/occlusion, then HRTF/effects, and performs a deterministic final mix. Equal-power pan uses fixed table/interpolation; spatial transforms use stable source ordering. CPU and offload share coefficients and immutable input layouts.

The offload scheduler batches only FFT/convolution, HRTF banks, long reverb, and Ambisonics/reflections. Setup compiles and pins kernels before start. For each period the CPU path produces or retains a safety result while the GPU works; a validated completion before 60% selects GPU output, otherwise CPU output is committed and the late token is discarded by epoch.

VirtIO sound uses control/event/tx/rx queues over the shared VirtIO transport. The audio service owns fixed PCM pools and sends generation-bound descriptors. HDA adapts its existing BDL/IRQ path to the same device contract. Application IPC maps bounded buffers, commits epochs, and receives completion/xrun/device events. Capture reverses period ownership.

Desktop capsules use direct OS APIs through minimal ABI modules: PipeWire with ALSA fallback, CoreAudio, WASAPI, sndio with OSS-family fallback. Capability negotiation never silently substitutes a different API or mode.

For x86 QEMU host offload, enumerate matching QEMU ivshmem PCI functions in
stable bus/device/function order. Map ordinal `0` for render/host-GPU and
ordinal `1` for audio. Pass the ordinal into the BAR64 mapper so distinct
window bases are programmed. Absence of ordinal `1` makes audio offload
unavailable; it must not fall back to ordinal `0`.

## Error and resource model

Errors are typed as unavailable, unsupported, invalid-format, invalid-state, queue-full, stale-generation, malformed-completion, timeout, disconnected, underrun, overrun, and internal. All externally supplied lengths/counts are overflow-checked before mapping/allocation. Device loss is idempotent; teardown proves zero live handles, mappings, DMA descriptors, queues, callbacks, and offload tokens.

<!-- sdn-diagram:id=simpleos_io_audio_gpu_offload.design -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simpleos_io_audio_gpu_offload.design hash=sha256:auto render=ascii
@layout dag
@direction LR
Application -> CommandEpoch
CommandEpoch -> SpatialLowering
SpatialLowering -> CPURender
CPURender -> SafetyPeriod
CommandEpoch -> CoarseOffload
CoarseOffload -> DeadlineGate
SafetyPeriod -> DeadlineGate
DeadlineGate -> DevicePeriodRing
DevicePeriodRing -> CompletionEvent
DeviceLoss -> SafetyPeriod
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simpleos_io_audio_gpu_offload.design hash=sha256:auto
commands -> spatial -> CPU safety period ----+
commands -> coarse GPU work -> deadline gate +-> device ring -> completion event
```

</details>
<!-- sdn-diagram:end -->

## Observability

Receipts expose warm p95/p99 event latency, render/offload duration as period fractions, jitter, underruns/overruns, CPU/GPU utilization, PCM/parity hashes, maximum RSS, queue high-water marks, fallback reason/count, and resource totals. Environmental receipts bind target, host/guest ISA, accelerator, device/backend, binary/source hashes, argv, and evidence hashes.
