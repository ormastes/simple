# UNO Q QRB2210 Native Simple2D Admission

The desktop target is the QRB2210 MPU with Adreno 702, never the STM32U585
coprocessor. `QualcommBackend` reuses `VulkanBackend`; producers continue to
emit `DrawIrComposition` and no board-private drawing path is permitted.

Run `scripts/check/check-unoq-qrb2210-native-2d.shs --transcript FILE
--capture FILE` to preflight a receipt. The checker verifies the capture hash
and delegates all semantic decisions to the Pure-Simple admission owner. Once
the canonical port exists it may report at most `ready` with
`offline-untrusted`: caller-supplied files cannot prove a physical board. A
future live runner must itself acquire the serial stream
and frame before it may claim PASS. The admission contract requires correlated
Adreno Vulkan submission, fence and device readback, exact checksum, no CPU
fallback, left/right Ctrl and Alt, pointer move/down/drag/up/wheel, and completed
non-silent audio. It also requires ordinary key down/up, at least two animation
frames, DrawIR work, and font glyph work. A Debian/Android board run is readiness
only.

Today the canonical `uno_q_desktop_contract` reports the QRB2210 SimpleOS
display/input/audio port unavailable, so even a semantically complete offline
receipt is blocked before readiness promotion. Do not change the admission to
bypass that owner; the port implementation must update the canonical contract.

This host had no authorized ADB device on 2026-08-09, so no live board claim is
made. Remaining external work is the QRB2210 SimpleOS boot/display/Adreno
firmware, MMU/cache, queue and fence bring-up, followed by a real transcript and
capture from the physical board.
