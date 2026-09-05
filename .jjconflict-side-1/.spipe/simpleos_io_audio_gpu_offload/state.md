# Feature: SimpleOS I/O, Audio, and GPU Audio Offload

## Raw Request
`$sp_dev events works? and qemu simple os io event handling may should use full pure simple as well as simple audio. 1. research qemu audio and io. make pure simple drivers and simple io, simple audio. research simple audio can access through simple 2d/3d for 3d sounds. and can direct access. and design gpu offload simple audio to what to support for offload. research and plan/design than impl with high coverage of tests and env tests of qemu and linux verify and make mac, win, bsd too.`

## Task Type
feature

## Refined Goal
Deliver a pure-Simple event, I/O, and audio subsystem that operates directly and through Simple 2D/3D spatial-audio APIs, supports designed and implemented GPU/DSP audio offload with deterministic CPU fallback, and has fail-closed native evidence across SimpleOS QEMU, Linux, macOS, Windows, and BSD.

## Acceptance Criteria
- AC-1: Local and domain research documents inventory the existing event, QEMU device, SimpleOS I/O, audio, 2D/3D, spatial-audio, and accelerator surfaces; compare QEMU audio/I/O devices and host backends; and identify authoritative platform APIs for Linux, macOS, Windows, and BSD.
- AC-2: Feature and NFR option documents give pros, cons, effort, compatibility, latency, determinism, memory, security, and portability tradeoffs; the user selects the final requirements before architecture or implementation is accepted.
- AC-3: Architecture and detail-design documents define ownership and stable interfaces for `SimpleEventDevice`, `SimpleIoDevice`, `SimpleAudioDevice`, `SimpleAudioGraph`, `SimpleSpatialAudio`, and `SimpleAudioOffloadDevice`, including lifecycle, concurrency, buffer ownership, clocking, error handling, hot paths, and CPU fallback.
- AC-4: SimpleOS QEMU boots use pure-Simple guest drivers and guest-resident Simple event/I/O/audio code for the selected virtual devices; retained serial/guest evidence proves input events and deterministic audio-buffer production without substituting host `bin/simple`, fixed-command stubs, or Rust runtime implementations.
- AC-5: Direct Simple audio APIs can enumerate/open/close devices, negotiate formats, stream playback and capture where supported, report underrun/overrun/device-loss events, and recover or fail deterministically.
- AC-6: Simple 2D can play positioned stereo/panned sounds and Simple 3D can play listener/source spatial sounds with documented coordinates, attenuation, doppler, mixing, and channel-layout behavior; both lower through the shared audio graph rather than private backend paths.
- AC-7: GPU/DSP offload supports only the operations selected from measured research, exposes capability negotiation and immutable work descriptions, preserves observable CPU-reference semantics within selected tolerances, and falls back without audio discontinuity when unavailable, rejected, timed out, or device-lost.
- AC-8: Event handling has executable coverage for keyboard, pointer, controller, audio completion/xrun/device-change, ordering, timestamps, backpressure, cancellation, and shutdown across direct APIs, SimpleOS QEMU, and supported desktop backends.
- AC-9: Unit and integration tests achieve at least 80% branch coverage for new owned pure-Simple modules and include deliberate-red calibration, malformed input, boundary formats, lifecycle faults, concurrency/resource checks, CPU/offload parity, and no placeholder assertions or stubs.
- AC-10: Step-based SSpec environmental scenarios and generated operator manuals cover QEMU and native Linux, while macOS, Windows, and BSD rows each have fresh native PASS evidence or remain fail-closed with an authoritative TODO and resume plan naming prerequisites, exact commands, retained artifacts, owner, and final reviewer; unavailable rows are never counted as PASS.
- AC-11: Performance evidence measures end-to-end event latency, audio callback/render latency, jitter, underruns, warm p95/p99, maximum RSS, and CPU/GPU utilization on realistic fixtures; all selected NFR thresholds pass on applicable native and QEMU rows.
- AC-12: Pure-Simple provenance gates prove production wrappers run cached compiled pure-Simple artifacts and that normal run/test/SPipe evidence is not produced by a Rust seed, host-side guest substitute, stale binary, or raw-source production entrypoint.
- AC-13: Platform implementations and manifests cover Linux, macOS, Windows, BSD, and SimpleOS without silently aliasing unsupported APIs; build/check tests prove each target compiles and capability reports match the actual implementation.
- AC-14: Final verification passes environment/process audits, stub and duplication scans, requirement-to-test traceability, architecture and design freshness, generated-manual quality, relevant SimpleOS mission-critical gates, and the release-bound whole interpreter suite.
- AC-15: Any changed workflow, evidence wrapper, platform setup, or SPipe contract is reflected in matching `doc/07_guide`, `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, and `.gemini/commands` surfaces before verification.

## Scope Exclusions
No platform row, capture direction, spatial-audio path, or offload fallback is excluded yet. Codec authoring, DAW editing UI, and proprietary hardware-specific acceleration are excluded unless requirement selection explicitly adds them.

## Cooperative Review
This is a broad multi-platform hardware/runtime lane. Planned sidecars: Codex Spark for repository/platform inventory, Claude Haiku for QEMU device/backend comparison, and Claude Sonnet for audio/spatial/offload literature review. Merge owner: primary Codex agent. Final reviewer: normal/highest-capability Codex. Shared interfaces: `SimpleEventDevice`, `SimpleIoDevice`, `SimpleAudioDevice`, `SimpleAudioGraph`, `SimpleSpatialAudio`, `SimpleAudioOffloadDevice`. Manual flow helpers: `step("Boot the guest with the selected virtual devices")`, `step("Open the event and audio endpoints")`, `step("Render the deterministic audio scene")`, `step("Exercise accelerator negotiation and CPU fallback")`, and `step("Retain platform evidence and resource receipts")`. Setup/checker helpers: `prepare_simpleos_io_audio_qemu`, `check_simple_audio_backend`, `check_spatial_audio_parity`, `check_audio_offload_fallback`, and `check_io_audio_platform_matrix`. Every not-yet-implemented scenario helper must use `fail("not implemented")` rather than a passing placeholder. Generated-manual review owner: primary Codex agent, followed by final normal/highest-capability review.

## Research Summary

### Existing Code
- `src/os/drivers/virtio/virtio_input_ops.spl:237-360` and `src/os/lib/driver_runtime/event_loop.spl:37-129` provide pure-Simple guest input and event multiplexing.
- `src/os/drivers/audio/hda_controller.spl:27-624`, `hda_dma_resources.spl:6-123`, and `audio_service.spl:53-171` provide pure-Simple HDA bring-up, DMA, IRQ, and silent output.
- `src/lib/common/engine/audio/sound_synth.spl:28-275` plus `src/lib/nogc_sync_mut/engine/audio/` provide pure synthesis, graph, HRTF, doppler, occlusion, and effects.
- `src/runtime/runtime_audio.c:160-678` and `runtime_sdl2.c:81-178` show hosted device output remains native C/miniaudio or SDL2.
- `scripts/check/check-simpleos-wm-fullscreen-evidence.shs:755-1484` proves QEMU input receipts and HDA periods, not application PCM delivery.

### Reusable Modules
- Shared event route/epoch/replay contracts, audio graph/bus/spatial math, WAV codecs, HDA PCI/MMIO/DMA/IRQ, QEMU provenance wrappers.

### Domain Notes
- QEMU offers virtio-snd plus legacy HDA and VirtIO/USB/PS2 input; native host APIs differ across PipeWire/ALSA, CoreAudio, WASAPI, sndio/OSS.
- GPU compute is suitable for coarse prewarmed convolution/FFT/HRTF/Ambisonics, not callback clocking or tiny mixes; CPU semantics and bounded fallback remain mandatory.

### Open Questions
- NONE — user selected the full robust feature set and robust low-latency NFR profile on 2026-08-02.

<!-- sdn-diagram:id=simpleos_io_audio_gpu_offload.state_research -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=simpleos_io_audio_gpu_offload.state_research hash=sha256:auto render=ascii
@layout dag
@direction LR
Events -> SharedGraph
DirectAudio -> SharedGraph
Engine2D -> SharedGraph
Engine3D -> SharedGraph
SharedGraph -> CPUReference
SharedGraph -> OptionalOffload
CPUReference -> DesktopAndSimpleOSDevices
OptionalOffload -> CPUReference
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=simpleos_io_audio_gpu_offload.state_research hash=sha256:auto
Events/direct/2D/3D -> shared graph -> CPU reference / optional offload -> devices
```

</details>
<!-- sdn-diagram:end -->

## Requirements
- REQ-1 (AC-1/2): Preserve research traceability and user-selected feature/NFR policy — area: `doc/01_research/`, `doc/02_requirements/`.
- REQ-2 (AC-3/5): One explicit device/graph lifecycle supports direct playback/capture and deterministic faults — area: `src/lib/common/engine/audio/`, `src/os/services/audio/`.
- REQ-3 (AC-4/8): Pure-Simple QEMU guest drivers deliver ordered input/audio events and application PCM — area: `src/os/drivers/`, `src/os/compositor/`.
- REQ-4 (AC-6): Engine2D and Engine3D spatial adapters lower through the shared graph — area: `src/lib/*/engine/audio/`, `src/lib/*/game2d/audio/`.
- REQ-5 (AC-7): Capability-negotiated audio offload preserves CPU-reference semantics and bounded fallback — area: `src/lib/*/engine/audio/`, `src/lib/*/gpu/`.
- REQ-6 (AC-9/10/11): Coverage, environmental, resource, latency, jitter, underrun, and parity evidence is fail-closed — area: `test/`, `scripts/check/`.
- REQ-7 (AC-12/13): Linux/macOS/Windows/BSD/SimpleOS report honest target capabilities and pure-Simple provenance — area: `src/app/io/`, `src/os/`.
- REQ-8 (AC-14/15): Verification, manuals, guides, and workflow contracts remain current — area: `doc/06_spec/`, `doc/07_guide/`, agent/skill commands.

## Architecture

- Six stable virtual capsules: `SimpleEventDevice`, `SimpleIoDevice`, `SimpleAudioDevice`, `SimpleAudioGraph`, `SimpleSpatialAudio`, and `SimpleAudioOffloadDevice`.
- One CPU-normative immutable graph owns direct/2D/3D semantics; platform and QEMU drivers are leaf adapters.
- VirtIO sound is the cross-architecture QEMU primary; HDA remains x86 compatibility.
- Only prewarmed coarse convolution/HRTF/reverb/Ambisonics work offloads; callbacks, clocks, event order, tiny mixes, and final output remain CPU-owned.
- Resource and period ownership use generation-bound bounded state machines with fail-closed teardown.

## Specs

### Spec Files
- `test/03_system/io_audio/simple_audio_graph_spec.spl` — shared graph, spatial, lifecycle, faults, resources.
- `test/03_system/os/qemu/simpleos_io_audio_spec.spl` — guest input, VirtIO sound, HDA, provenance.
- `test/03_system/io_audio/simple_audio_platform_offload_spec.spl` — native capsules, offload, fallback, NFR matrix.

### Generated Manuals
- `doc/06_spec/03_system/io_audio/simple_audio_graph_spec.md` — complete, 0 stubs.
- `doc/06_spec/03_system/os/qemu/simpleos_io_audio_spec.md` — complete, 0 stubs.
- `doc/06_spec/03_system/io_audio/simple_audio_platform_offload_spec.md` — complete, 0 stubs.

### Manual Shape

Primary direct/2D/3D, QEMU guest, native backend, and offload flows are visible with log captures. Lifecycle faults, cross-architecture/platform matrices, provenance rejection, and resource teardown are folded. QEMU setup is inline and expanded into the guest flow with `@prev`.

### AC Coverage Matrix

| AC | Specs |
|---|---|
| AC-1..3 | research/requirements plus all three specs |
| AC-4, AC-8, AC-10, AC-12 | `simpleos_io_audio_spec.spl` |
| AC-5, AC-6 | `simple_audio_graph_spec.spl` |
| AC-7, AC-11 | `simple_audio_platform_offload_spec.spl` |
| AC-9, AC-13..15 | all three specs plus aggregate verification plan |

## Phase
spec-done

## Log
- dev: Created state file with 15 acceptance criteria (type: feature).
- research: Found 8 reusable subsystem groups, 12 primary evidence surfaces, and 8 mapped requirements; options await user selection.
- requirements: User selected F1-A/F2-A/F3-A/F4-A/F5-A with NFR-B; final requirements written and option drafts removed.
- arch: Designed six virtual capsules, one shared graph, QEMU drivers, platform leaves, and bounded CPU/offload fallback.
- spec: Created three executable scenario manuals with 11 scenarios, 0 doc stubs, and full AC/REQ/NFR traceability.
- implement: Partial — added pure-Simple graph/format, convolution/offload fallback, period-ring, unified device-event, platform lifecycle, and VirtIO sound protocol slices. Twenty-seven focused examples pass under the available Rust-seed runner; native capsules, QEMU device/service integration, physical Vulkan audio kernels, cross-host evidence, coverage, and self-hosted verification remain active.
- implement: Extended x86 HDA from silent-only DMA to bounded application PCM submission, added pure signed-16 packing, a guest desktop calibration receipt, and fail-closed static/live wrapper gates. Thirty-three focused examples and the x86 QEMU preflight pass under seed-attributed tooling; a fresh admitted pure-Simple QEMU boot is still required.
- implement: Added a safe hosted interpreter MMIO/DMA simulator so pure-Simple driver lifecycle tests resolve bare-metal provider externs without dereferencing host addresses. Rust provider/dispatch tests pass (3/3), the canonical MMIO spec passes, and VirtIO-input reaches 7/8 after exercising negotiation, DMA release, queue rejection, event recycling, IRQ acknowledgement, and malformed-ring shutdown; the redundant optional-presence matcher was removed after the three-cycle cap and awaits a fresh-session rerun.
- implement: Fresh hosted verification passes VirtIO-input 8/8 and VirtIO-snd service 4/4. Added selector-banked VirtIO MMIO simulation, a lean freestanding input wire contract, and non-optional poll receipts; AArch64 diagnostic Stage 2 now links and boots a 168 KB guest instead of failing on enum/runtime symbols. Live transport discovery still fails before input/audio receipts; the wrapper now rejects `simple-bootstrap` as production evidence and binds compiler identity, while the next run will expose numeric input readiness and the sound transport failure detail.
- implement: Three bounded AArch64 diagnostic boots isolated keyboard ready, pointer capability lookup failure, and a zeroed VirtIO-snd DMA queue. QEMU source confirms vendor/product IDs `0627:0001/0002/0003` and REL_X/REL_Y mouse capabilities, so the pure-Simple input path now has a device-ID fallback. Sound DMA failures preserve raw mapping values and do not negotiate hardware after allocation failure. Focused input/DMA/service specs pass 8/8, 3/3, and 4/4; the next fresh QEMU run must determine the raw DMA failure and validate pointer delivery.
- implement: Production AArch64 and RISC-V QEMU rows now PASS with provenance-verified pure-Simple Stage 3 compiler `8da1c614693074457bff5586f60f2047f1dfe3c5dabd9e4b928aea21bcb71d29`. Both rows prove ordered keyboard/pointer delivery, VirtIO-snd `driver_ok`, non-silent PCM, period completion, and DMA-clean shutdown. RISC-V fixes include architecture-specific MMIO bounds, allocation-free input polling, direct 32-bit PCM parameter serialization, bounded dynamic arrays, and a 1 MiB linker-accounted heap. Aggregate x86_64 VirtIO/HDA evidence and the release-wide self-hosted suite remain open; `check-simpleos-io-audio-qemu.shs --live` currently fails closed when those logs are absent.
