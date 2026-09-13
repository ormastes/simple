# Slang bounded prefix cache live evidence blocked by runtime
**Status:** OPEN (unverified 2026-09-12)

Date: 2026-09-08. Status: open environment blocker.

The clean `origin/main` worktree's canonical `bin/release/simple --version`
fails its bounded identity probe because the deployed
`aarch64-unknown-linux-gnu/simple` executable is unavailable. Per repository
policy, the Rust seed was not substituted.

Consequences:

- The optimizer app could not run on the touched `.spl` backend/engine files.
- A live Simple import-closure check could not be admitted.
- Real-model cached/uncached output parity, interleaved latency, and maximum RSS
  remain unmeasured.

Available evidence is limited to the deterministic stateful shim contract and
successful compilation/export against the installed llama.cpp SDK. Close this
blocker only with an admitted self-hosted runtime and a runnable small GGUF,
then retain provenance, fallback state, raw samples, p50/p95, maximum RSS, and
output checksums.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
