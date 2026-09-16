# TLDR: Hosted WM Capture Lowering Failure
## Obsolete 2026-09-16 — TLDR duplicate of same-named main entry; same symptom+area

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

Canonical host capture is blocked before rendering because the self-hosted
compiler loses `width` while lowering `HostedCaptureFramebuffer.put_pixel` and
then reports `put_pixel` missing. No synthetic capture is accepted as evidence.

