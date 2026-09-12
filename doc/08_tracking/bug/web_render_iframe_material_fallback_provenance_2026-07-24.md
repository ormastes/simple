# Nested iframe material fallback provenance

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

The top-level Simple Web layout and Draw IR render paths now attach typed,
realized solid-material fallback provenance to `WebRenderArtifact`. Nested
`srcdoc` iframe pixels are composited by the software child renderer, but their
fallback sidecars are not yet aggregated into the parent artifact.

The shared WM theme wrapper is top-level and is therefore covered. A follow-up
should define deterministic parent/child evidence ordering and hash composition
before nested iframe provenance is exposed.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
