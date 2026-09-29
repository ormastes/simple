<!-- codex-design -->
# Simple 2D Multiplatform Vulkan Hardening Detail Design

This design implements the architecture freeze in
`doc/04_architecture/simple_2d_multiplatform_vulkan_hardening.md`. It makes no
source change and records no live-render PASS.

## Fixed transitions and receipts

```text
InputEvent + optional VirtioSnd completion
  -> semantic action / WM state epoch
  -> DrawIrComposition(revision, commands, resources)
  -> submit(run_id, frame_id, request_generation)
  -> fence + device readback
  -> execution/frame receipt
```

All terminal receipts carry the immutable `(session_generation, run_id,
frame_id, request_generation, completion_generation)` correlation tuple. A
receipt may be used only when it matches the submitted tuple, the requested
backend, expected dimensions/pixel count, and the selected environment profile.
Zero, stale, cross-session, duplicated, or reordered values are rejects.

### Capability versus execution

`GpuProviderCapabilityReceipt` is allowed to report `unavailable`,
`transport-ready`, `venus-discovered`, or cached `physical-device-admitted`.
It has no executable pixels. `GpuExecutionReceipt` is eligible for Vulkan
promotion only at `device-executed/readback-proven` and must contain: selected
Vulkan backend; positive native handle and physical identity; fence terminal
status; `device_readback`; output bytes/pixel count/checksum; complete command
coverage; and CPU-oracle equality. HELLO populates only the first receipt.

### Lifecycle protocol

1. A startup discovery owner acquires a runtime lease, identifies a physical
   device within the bounded HELLO budget, and retains that lease.
2. Every execution owner acquires its own lease before it initializes/shares an
   Engine2D Vulkan session. It verifies the selected physical device again.
3. A frame owns command/resources until its fence is terminal and readback is
   copied into the correlated receipt. Shutdown/cancellation quarantines then
   cleans any submitted resources before release.
4. The final release alone waits idle and destroys global runtime resources.
   Early setup failure releases exactly the resources/lease it acquired.
5. Device loss, reset, protocol/config generation change, or daemon restart
   invalidates discovery, retained images/font material, and all receipts.

No probe, HELLO, renderer construction, or ProcessingIR request may release a
different owner's lease. Daemon shutdown is serialized after in-flight work;
the discovery lease is not released during an execution request.

## DrawIR and font design

The executor accepts immutable command/resource snapshots. It preserves command
order, clip, opacity, source-over semantics, and image coverage. A renderer
either lowers every command in its declared matrix or returns an explicit
unsupported/failure receipt before presentation. It may not count a skipped
command as rendered.

Font flow is semantic DrawIR text/glyph-run -> `draw_text` -> transient
`FontRenderer.prepare_selected_glyph_run*` -> `FontRenderBatch`/atlas upload.
The atlas key includes resolved font identity, DPI/size, glyph/run revision and
device session. It is bounded and invalidated at the lifecycle points above.
DrawIR never holds its atlas handle or cache contents. Text evidence joins the
font identity/batch status to the same frame receipt and its device readback.

Persistent resources are revision-keyed: a daemon session, Engine2D session,
pipeline/descriptor cache, image table, and atlas live across unchanged frames.
The hot path cannot rescan discovery, spawn a process, compile a pipeline, or
allocate a new full-frame buffer. Damage/revision changes decide which command
or resource needs upload. Measurements record cold first frame separately from
20 warm post-oracle frames; p95 is nearest-rank and RSS includes daemon + QEMU.

## ARM atomic IO receipt design

`Arm64WmIoReceiptOwner` accepts already-decoded `VirtioInputEvent` and
`VirtioSndServiceReceipt`/`VirtioSndCaptureReceipt`; it neither touches DMA nor
parses evdev. The staged API is:

```text
begin(session_generation, event_seq)
  -> accept_input(normalized event, modifier bitmap)
  -> accept_wm(action/target/reason, state_epoch, frame_id)
  -> accept_audio(optional stream/direction/session/generation/hash)
  -> publish(frame request/completion correlation) -> Arm64WmIoFrameReceipt
```

`publish` succeeds only once. It requires one input and WM mutation result; it
requires audio only for an audio-requesting scenario. It rejects a stale
VirtIO-SND completion, mismatched stream/session/generation, an input sequence
gap/replay, absent Ctrl/Alt state when the event declares it, invalid frame
correlation, or a second publish. `not_requested` is encoded rather than
silently omitted. The eventual owner is a coordinator over existing
`src/os/kernel/arch/arm64/virtio_input.spl`,
`src/os/compositor/arm64_virtio_input_backend.spl`,
`src/os/services/audio/virtio_snd_service.spl`, and WM executor owners.

## Native dispatch admission requirement

Before a QEMU draw request is promoted, the native compiler regression must
prove that dispatch selects a vtable only from canonical nominal type evidence
and an initialized implementation vtable. The qualified-struct-layout repair
at `8799862139ea` is an upstream prerequisite, not the final class-dispatch
proof. A mixin/duck render target must be converted by an explicit concrete
adapter or rejected; unsafe native dispatch cannot be hidden behind a fallback.

## Environment runbook and evidence

| Environment | Run only when | Required resulting evidence |
|---|---|---|
| Linux | admitted native compiler, Vulkan loader/device, daemon executable | fresh HELLO plus one DrawIR submit/fence/readback, oracle/capture, warm p95/RSS |
| ARM64 QEMU | Linux prerequisites plus booted guest/BAR/input/audio devices | guest/daemon correlation, atomic IO receipt, DrawIR text/animation capture, device bytes |
| macOS | approved macOS host and native toolchain/runtime | native receipt/capture; this Linux host records only unsupported/emulator preparation |
| UNO Q | enumerated attached board and native board runner | firmware/device/queue/fence/readback/display identity and board-attached capture |

The `simpleos_2d_showcase` is accepted only when animation changes correlated
frames, pointer/button/drag/wheel and keyboard with both Ctrl/Alt sides produce
the intended semantic result, audio playback/capture completes when requested,
and font text is present in the exact device-readback frame. Screenshots without
the matching receipt are presentation artifacts, not evidence.

## Implementation order

1. Land/re-run the nominal dispatch compiler proof and bounded first DrawIR
   replay without altering the protocol.
2. Implement the common capability facade as a thin projection of existing
   discovery/execution facts; add no Venus parsing to it.
3. Finish Venus private protocol -> queue -> fence -> readback, then permit the
   compositor adapter to consume a common proven receipt.
4. Implement the ARM atomic coordinator, reuse existing input/audio owners,
   and add receipt validation before any new QEMU scenario.
5. Run the showcase/capture and performance rows. macOS/UNO Q remain explicit
   external-host/physical-board work until their prerequisites are true.
