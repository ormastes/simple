# Nested iframe material fallback provenance

Status: open, non-blocking for the shared-WM theme path.

The top-level Simple Web layout and Draw IR render paths now attach typed,
realized solid-material fallback provenance to `WebRenderArtifact`. Nested
`srcdoc` iframe pixels are composited by the software child renderer, but their
fallback sidecars are not yet aggregated into the parent artifact.

The shared WM theme wrapper is top-level and is therefore covered. A follow-up
should define deterministic parent/child evidence ordering and hash composition
before nested iframe provenance is exposed.
