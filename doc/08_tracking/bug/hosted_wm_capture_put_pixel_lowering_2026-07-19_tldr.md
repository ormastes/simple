# TLDR: Hosted WM Capture Lowering Failure

Status: DUPLICATE of hosted_wm_capture_put_pixel_lowering_2026-07-19.md
Status re-verified 2026-08-17 by source inspection (triage shard 01).

Canonical host capture is blocked before rendering because the self-hosted
compiler loses `width` while lowering `HostedCaptureFramebuffer.put_pixel` and
then reports `put_pixel` missing. No synthetic capture is accepted as evidence.
