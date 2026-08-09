# UNO Q QRB2210 Native Simple2D Admission

The desktop target is the QRB2210 MPU with Adreno 702, never the STM32U585
coprocessor. `QualcommBackend` reuses `VulkanBackend`; producers continue to
emit `DrawIrComposition` and no board-private drawing path is permitted.

Run `scripts/check/check-unoq-qrb2210-native-2d.shs --transcript FILE
--capture FILE` to preflight a receipt. The checker verifies the capture hash
and delegates all semantic decisions to the Pure-Simple admission owner. Once
the canonical port exists it may report at most `ready` with
`offline-untrusted`: caller-supplied files cannot prove a physical board. A
The live runner is
`scripts/check/run-unoq-qrb2210-native-2d-live.shs`. It accepts only device,
output-directory, and timeout selection; transcript, receipt, capture, replay,
and offline inputs are rejected. It selects an authorized ADB device, verifies
QRB2210/UNO Q identity, invokes `/usr/bin/simpleos-unoq-2d-evidence` on the
board, first clears the fixed remote evidence paths, and acquires both the
serial receipt and raw RGBA capture into a fresh private run directory. Missing
hardware or a missing/failing production provider remains `blocked`; an
offline preflight can never be promoted to PASS. The admission contract requires correlated
Adreno Vulkan submission, fence and device readback, exact checksum, no CPU
fallback, left/right Ctrl and Alt, pointer move/down/drag/up/wheel, and completed
non-silent audio. The live runner strengthens this to exactly 20 animation and
20 warm performance frames, a nonzero warm p95 no
greater than the host-owned 16,700 us budget, a nonzero peak RSS no greater
than the host-owned 256 MiB budget,
DrawIR work, font glyph work, exact raw-capture byte count/hash, and matching
run/ADB/boot/frame identities. The boot ID is read independently before and
after provider execution, the readback byte count must equal the acquired
capture, and admission runs only through a canonical Stage4 provenance-verified
pure-Simple CLI. A Debian/Android board run is readiness
only.

Today the canonical `uno_q_desktop_contract` reports the QRB2210 SimpleOS
display/input/audio port unavailable, so even a semantically complete offline
receipt is blocked before readiness promotion. Do not change the admission to
bypass that owner; the port implementation must update the canonical contract.

The QRB2210 boot target is
`examples/09_embedded/simple_os/arch/qrb2210/gui_entry_desktop.spl`. At present
it intentionally terminates with `UNO_Q_QRB2210_DESKTOP_BLOCKED` after querying
the canonical display, window-event, and audio capabilities. It must not be
replaced with the ARM QEMU desktop entry: RAMFB, virtio-input, ivshmem host GPU,
and virtio-snd are QEMU transports, not Uno Q hardware. The entry also refuses
to manufacture an `UnoQNative2dEvidence` record; PASS evidence must originate
from the eventual physical composition root and live-board runner.

This host had no authorized ADB device on 2026-08-09, so no live board claim is
made and the live runner was not executed against hardware. Remaining external work is the QRB2210 SimpleOS boot/display/Adreno
firmware, MMU/cache, queue and fence bring-up, followed by a real transcript and
capture from the physical board.
