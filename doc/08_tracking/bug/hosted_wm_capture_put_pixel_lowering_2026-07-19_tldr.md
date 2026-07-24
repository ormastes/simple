# TLDR: Hosted WM Capture Lowering Failure

Canonical host capture is blocked before rendering because the self-hosted
compiler loses `width` while lowering `HostedCaptureFramebuffer.put_pixel` and
then reports `put_pixel` missing. No synthetic capture is accepted as evidence.
