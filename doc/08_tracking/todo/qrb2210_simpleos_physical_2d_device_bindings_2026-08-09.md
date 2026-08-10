# QRB2210 SimpleOS physical 2D device bindings

Status: blocked on physical QRB2210 SimpleOS driver bring-up and an attached
UNO Q. This is not satisfied by ADB transcripts, Debian/Android observations,
QEMU devices, replay files, or constructed receipt objects.

Implemented source boundary:

- board/boot/device-node/native-handle/driver-generation identity;
- evdev move/down/drag/up/wheel/key normalization to canonical
  `HostInputEvent`, including separate left/right Ctrl and Alt evidence;
- PCM submit/completion correlation by physical buffer and exact sample count;
- display present/capture correlation by physical handle, frame, present ID,
  byte count, and device-readback checksum.
- Vulkan submit/fence/readback correlation by one GPU boot/device/generation,
  exact command-buffer/device/queue/fence/readback handles, and frame identity.

Remaining physical work:

- SimpleOS QRB2210 DRM/KMS or board display device node must mint the display
  handle and hardware present/capture receipts;
- SimpleOS QRB2210 input device nodes must mint monotonically sequenced evdev
  receipts from real pointer and keyboard interrupts. The physical adapter now
  exists in `os.port.qrb2210_evdev_primitive_provider`: it requires a bound
  IRQ line, kernel-owner and event-ring handles, boot/device/generation identity,
  monotonic interrupt and event sequences, and a nonzero interrupt timestamp. It remains
  unavailable until the QRB2210 kernel input driver supplies that owner;
- SimpleOS QRB2210 audio device node must submit PCM DMA and mint completion
  receipts only after the hardware completion interrupt;
- Adreno Vulkan submit/fence/readback owners must bind the already-landed GPU
  ports and retain the same boot/device generation identity;
- the canonical desktop capability owner may change status to OK only after
  all providers are bound and live-board evidence validates their receipts.

## PCM DMA lower-owner audit (2026-08-10)

No concrete `Qrb2210PcmDmaKernelPort` can be implemented from the current
in-tree hardware APIs without fabricating QRB2210 behavior. The repository has
the following reusable primitives:

- syscall 84/85 DMA allocation/free and syscall 86/87 CPU/device cache
  synchronization in `os.kernel.ipc.syscall_device`, with user-facing
  descriptor wrappers in `os.userlib.device` and scalar ABI shims in
  `os.kernel.abi.syscall_shim_device`;
- physical/virtual/allocation identity validation in
  `os.kernel.ipc.dma_alloc_contract` and DMA ownership types in
  `os.kernel.types.device_mem_types`;
- descriptor/cache-policy and bounded registry models in
  `os.drivers.dma.dma_descriptor`; these model ownership and required sync
  direction but do not perform QRB2210 DMA programming;
- generic IRQ port/table scaffolding in `os.kernel.interrupts.ports` and
  `os.kernel.arch.common.interrupt_dispatch`, plus a GICv2 handler table in
  `os.kernel.arch.arm64.interrupt`. The latter currently pins QEMU `virt` GIC
  addresses and is not itself a QRB2210 board IRQ owner;
- device-specific transport examples for HDA and VirtIO-snd. These are
  different hardware transports and are not valid UNO Q substitutes or
  evidence that either transport is physically ready here.

The required QRB2210-specific lower layer is absent. In particular, there is
no checked-in authoritative board audio description, audio-controller/codec
probe, clock/reset/power-domain owner, IOMMU stream binding, playback DMA
channel implementation, PCM register/descriptor programming, or physical
audio IRQ handler. There is also no kernel device registry operation that
mints the contract's `/dev/snd/pcmC0D0p` `Qrb2210BoardDeviceHandle` and its
boot-scoped driver generation. Repository searches for QRB2210/QCS2290
Qualcomm audio controller,
LPASS, MI2S, SoundWire, and WSA bindings find no SimpleOS implementation.

Generic `rt_dma_*`, HDA, VirtIO-snd, QEMU, hosted ALSA, ADB output, or
constructed receipts must not be wired into `Qrb2210PcmDmaKernelPort`: none can
prove that physical UNO Q PCM reached the codec or that a QRB2210 completion
interrupt occurred.

### Concrete staged bring-up

1. Add a board-authoritative QRB2210 audio manifest derived from the shipped
   UNO Q firmware/device tree. It must pin the actual controller and codec
   compatibles, MMIO ranges, IRQ/GIC specifier, clocks, resets, power domains,
   IOMMU stream IDs, DMA request/channel IDs, and output route. Reject unknown
   or incomplete manifests.
2. Implement a pure-Simple kernel hardware owner under
   `src/os/drivers/audio/qrb2210/`. Its probe must acquire and verify those
   resources, bind one boot-scoped owner/generation, configure exactly signed
   16-bit interleaved 48 kHz mono/stereo playback, expose the exact IRQ,
   kernel-owner, submit-ring, completion-ring, DMA-pool, period, and maximum
   frame identity required by `Qrb2210PcmDmaKernelIdentity`, and remain
   unavailable on every partial initialization path.
3. Allocate the period ring through the kernel DMA API, retain CPU/device and
   allocation identities, apply syscall-86 CPU-to-device cache
   synchronization, copy only whole validated periods, program the real
   playback DMA descriptors,
   and ring the documented hardware doorbell. Keep at most the provider's one
   admitted submission in flight. A submission receipt may be minted only
   after the controller accepts that descriptor, and must reproduce every
   field checked by `qrb2210_pcm_submit_correlates`.
4. Bind the board-described GIC controller and register the physical audio IRQ
   through an AArch64 path that does not reuse the QEMU `virt` MMIO constants.
   The handler must read and acknowledge the controller's real completion
   status, advance monotonic IRQ/completion sequences, attach a nonzero interrupt timestamp,
   and publish completion only for the exact submitted allocation and frame
   range and checksum. The completion-ring identity must match the advertised
   kernel identity, and every receipt field must satisfy
   `qrb2210_pcm_completion_correlates`. Polling a software counter is not
   completion evidence.
5. Make the lower owner (directly or through one thin adapter) implement
   `Qrb2210PcmDmaKernelPort` and install a `Qrb2210PcmDmaAudioProvider` backed by
   it into the QRB2210 composition root. Keep both lower-owner and provider
   `readiness_status()` at `UNO_Q_DESKTOP_STATUS_PORT_UNAVAILABLE` until probe,
   DMA, IRQ, codec route, all nonzero ring/owner/pool handles, and exact
   boot/device/generation identity succeed.
6. Verify on an attached UNO Q with a non-silent multi-period sample: require
   exact submit/completion/buffer/checksum correlation, observed physical IRQ
   progress, replay and reboot rejection, underrun/error fail-closed behavior,
   and audible/capture evidence from the real board. Only that evidence may
   close this item or promote the audio capability.
