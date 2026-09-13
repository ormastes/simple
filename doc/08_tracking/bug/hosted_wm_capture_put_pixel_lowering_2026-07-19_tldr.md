# TLDR: Hosted WM Capture Lowering Failure

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Canonical host capture is blocked before rendering because the self-hosted
compiler loses `width` while lowering `HostedCaptureFramebuffer.put_pixel` and
then reports `put_pixel` missing. No synthetic capture is accepted as evidence.

## Triage 2026-09-12
TLDR record, older than 45 days, no cheap repro given. Closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
