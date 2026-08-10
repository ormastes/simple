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
  IRQ line, kernel event-ring handle, boot/device/generation identity, monotonic
  interrupt and event sequences, and a nonzero interrupt timestamp. It remains
  unavailable until the QRB2210 kernel input driver supplies that owner;
- SimpleOS QRB2210 audio device node must submit PCM DMA and mint completion
  receipts only after the hardware completion interrupt;
- Adreno Vulkan submit/fence/readback owners must bind the already-landed GPU
  ports and retain the same boot/device generation identity;
- the canonical desktop capability owner may change status to OK only after
  all providers are bound and live-board evidence validates their receipts.
