# macOS Bootstrap Reverse-Reference Harmonization NFR Selection

Status: SELECTED.

The user selected the baseline-relative 10% policy on 2026-09-02. Unchosen
absolute-numeric and monotonic-only policies are deleted.

- An admitted baseline receipt is required independently for `arm64` and
  `x86_64`.
- Maximum steady RSS across exactly 20 warm requests is baseline RSS × 110%.
- Maximum nonnegative RSS growth across those requests is baseline RSS × 10%.
- The receipt binds architecture, baseline evidence digest, producer and server
  digests, decision source, and this document digest.
- Missing, shared, inferred, stale, or digest-mismatched baselines fail closed.

The canonical decision source is
`user-final-performance-authority-2026-09-02`.
