# Engine2D Straight-Alpha Blend on Transparent Destinations

Status: open

`std.gpu.engine2d.color.blend` computes RGB as if the destination were opaque
while separately computing src-over alpha. For 50% straight-alpha white over
transparent black it returns approximately `0x80808080`; straight-alpha
src-over requires `0x80FFFFFF`. A later composite multiplies coverage again,
darkening antialiased vector-font fringes and any other translucent image drawn
over a transparent framebuffer.

Opaque destinations retain the established result, so current font scenarios
with an opaque clear do not discriminate this bug. Fix the shared blend owner,
then update CPU/GPU parity anchors and add an absolute transparent-destination
oracle before claiming transparent-surface font correctness.
