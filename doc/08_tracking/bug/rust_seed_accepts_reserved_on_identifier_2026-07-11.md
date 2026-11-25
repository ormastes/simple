# Rust Seed Accepts Reserved `on` Identifier
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

The Rust seed accepted `val on = ...` in `src/os/hosted/hosted_entry.spl`, while
the stage3 pure-Simple discovery parser rejected it with `expected pattern,
found On`. Source checks performed only with the seed therefore produced a
false green result.

Production code now uses `fullscreen_enabled`. Parser conformance should add a
shared negative fixture so seed and self-hosted frontends reject reserved
identifiers consistently with a source location.


## 2026-11-25 triage (p3-bap lane, Windows worktree)

Production fix confirmed at `origin/release/1.0.0` (47d6c5eddd5):
`src/os/hosted/hosted_entry.spl:235` uses `fullscreen_enabled`; no
`val on` binding remains in that file. The open remainder is a shared
seed/self-hosted parser negative fixture so both frontends reject reserved
identifiers consistently — Rust-seed parser conformance work, not actionable
in this lane. Status header ("needs owner triage") stands.
