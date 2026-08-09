# UNO Q QRB2210 Native Simple2D — Local Evidence

Repository inspection confirms two distinct UNO Q processors. The STM32U585
SimpleOS Lite target is a real MCU lane but cannot own a desktop, Adreno GPU,
window input, or audio. The QRB2210 MPU is the only eligible desktop target.

Reusable implementation already exists in `QualcommBackend`, which delegates
to `VulkanBackend`, and therefore preserves the shared Engine2D and DrawIR
owners. Missing SimpleOS-native QRB2210 work is below that boundary: boot and
display ownership, Adreno firmware, MMU/cache coherency, Vulkan queue/fence and
device readback, plus board input/audio drivers. An ADB-installed Debian or
Android artifact can establish board readiness but cannot establish SimpleOS.

Host probe on 2026-08-09 found `adb` installed and no authorized device. The
implemented admission and offline preflight consequently fail closed and make
no live board claim. Caller-supplied receipts remain untrusted readiness
evidence even when their semantics and capture hash validate. A later live
runner must acquire both streams itself without adding another renderer. The
admission also consumes `uno_q_desktop_contract`; because that canonical owner
still reports the QRB2210 SimpleOS port unavailable, synthetic complete evidence
cannot bypass it and remains blocked.

The canonical target entry now exists at
`examples/09_embedded/simple_os/arch/qrb2210/gui_entry_desktop.spl`. It is an
admission boundary, not a renderer: it checks display, window-event, and audio
through `uno_q_desktop_contract` and terminates before renderer construction
while any owner is unavailable. It deliberately does not import the ARM QEMU
RAMFB, virtio, ivshmem, or audio adapters. When physical drivers and a board
composition root are implemented, that root must reuse WM → DrawIR → Engine2D
→ Qualcomm Vulkan and feed live correlated receipts to the existing admission.

The next source slice types that lower boundary in
`os.port.qrb2210_native_2d_ports`: display, canonical `HostInputEvent`, PCM
audio, Engine2D command-batch submit, fence completion, and device-origin
readback remain distinct provider responsibilities. The matching
`qrb2210_native_2d_composition_root` admits only the shared WM -> DrawIR ->
Engine2D -> Qualcomm Vulkan route. No provider implementation was found or
added, and all six QRB2210 capability statuses remain `port-unavailable`.
