# Slang prefix-cache live evidence blocked by runtime provenance

Date: 2026-09-08. Status: open evidence blocker.

The clean KV-cache worktree has no admitted self-hosted Simple executable.
`bin/release/simple check src/lib/gc_async_mut/slang` rejected its local
deployed target during the bounded identity probe. The main worktree wrapper
also rejected its target as non-production. Per bootstrap policy, the Rust seed
was not substituted.

Consequently the C shim ABI and deterministic context behavior are verified,
but Simple import-closure execution, real-model output parity, interleaved
prefill latency, and maximum RSS remain unmeasured. Resolve by admitting a
current self-hosted runtime, then run the focused Slang source check and a small
real GGUF cached/uncached differential with at least one warmup and seven
interleaved samples. Do not treat this record as a performance result.
