# Stage4 Streaming Live-Slope Gate

The system contract binds
`scripts/check/check-stage4-selfhost-parse-memory-multifile.shs` to the exact
experimental Stage4 ownership configuration.

The runner generates a deterministic 40-file import chain, compiles it with a
source-matched pure-Simple binary, and accepts only when the build succeeds,
its producer attestation matches the current source content, all physical
sources emit unique contiguous release receipts, registry growth stays bounded,
and peak RSS remains below its ceiling. Rust-seed, timeout, compiler failure,
stale provenance, duplicate/missing receipts, wrong-directory receipts, slope
regression, and RSS regression are explicit failures. The bounded `--self-test`
executes marker parser fixtures plus canonical-lane and smoke-receipt checks.
Source attestation includes files under `examples/10_tooling` reached through
supported `src/app` aliases and rejects aliases escaping the owned source roots.
The production Stage 4 launcher explicitly enables both the low-memory profile
and streaming-surface path; the memory algorithm is not accepted from a
test-only environment override.

Executable source:
`test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl`.
