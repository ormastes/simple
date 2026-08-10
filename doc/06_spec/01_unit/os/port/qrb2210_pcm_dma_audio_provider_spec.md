# QRB2210 physical PCM DMA audio provider

This focused specification checks physical identity admission, bounded
non-silent S16LE payload validation, exact submit correlation, and exact
completion/replay/cross-boot rejection. It does not claim live board playback;
that requires a board-installed `Qrb2210PcmDmaKernelPort` implementation.
