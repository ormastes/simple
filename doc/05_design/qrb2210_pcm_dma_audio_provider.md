# QRB2210 PCM DMA Audio Provider

The provider implements the existing `Qrb2210AudioPort` behind a physical
SimpleOS kernel-owner boundary. It never opens hosted ALSA, uses QEMU, consumes
transcripts, synthesizes receipts, or promotes UNO Q readiness.

The kernel identity binds one QRB2210 boot and audio device generation to an
owner handle, submit ring, completion ring, DMA pool, fixed 48 kHz channel
geometry, period size, and an 8192-frame maximum. Submit accepts only aligned,
bounded, non-silent signed 16-bit PCM. The kernel receipt must reproduce the
exact device, owner, submit ring, DMA buffer, frame range, monotonic sequence,
sample count, and order-sensitive PCM checksum.

Only one buffer may be in flight. Completion must arrive from the bound
completion ring and match the submission, buffer, first frame, completed frame
and sample counts, checksum, submit sequence, fresh completion sequence,
completion identity, and interrupt timestamp. A mismatch returns no completion;
successful consumption clears the active submission, making replay fail closed.

Physical board readiness remains unavailable until a board-installed kernel
implementation of `Qrb2210PcmDmaKernelPort` reports ready with a valid identity.
