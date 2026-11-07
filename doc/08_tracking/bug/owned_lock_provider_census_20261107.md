# Owned lock provider census regression

PR #7755 introduced three canonical lock entrypoints with genuine C and Rust-delegating providers. Its post-merge Required Gates job `42371892497` reported those entrypoints as new single-lane symbols: the C implementation lived in an included `.h`, outside the C definition census.

The repair moves the unchanged implementation to an included `.c` and updates its three provider inclusions and three native fixture inclusions. It changes no function body, ABI, token registry, runtime selection, baseline, allowlist, or census extractor. The native runtime and Rust build use explicit source lists; this included implementation is not added as a separate translation unit.

Verification: `taskset -c 0-4 timeout 60s sh scripts/check/check-rt-dual-implementation-ratchet.shs --baseline-rev 8a8447fca5558257ef5861f6287526f923f294ae` passed once: 15 self-test fixtures, 2,605 symbols checked, zero new single-lane symbols. The base is the original PR base, so this checks the complete introduced API rather than hiding it in a newer baseline. Runtime execution remains NOT_RUN; this is a source-placement and gate-integration correction.
