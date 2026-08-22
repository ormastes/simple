# Simple compiler performance audit: missing admitted Stage 4 binary

## Status

Open blocker, observed 2026-08-22.

## Evidence

The isolated worktree `/mnt/data/worktrees/simple-compiler-performance-memory-audit`
has no `bin/simple` or `bin/release/x86_64-unknown-linux-gnu/simple`. The nearby
binary at `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
has SHA-256
`969fec3898b606ddffbfb629e1e427d086fb46448dfbea6a7caad287f260aedd` and
explicitly reports that it is a Rust-built bootstrap seed. It is therefore not
admissible under the repository's pure-Simple default-tooling rule.

One exploratory invocation of the focused vectorizer spec was stopped as
non-admissible evidence. It reported seven pre-existing fixture/semantic failures;
the output is not used as a baseline or acceptance result.

A provenance-matched pure-Simple Stage 2 candidate was subsequently found at
`/mnt/data/worktrees/private-rust-stage2.z0OiBs/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`.
Its SHA-256 is `83d9076a8b80ecf8e50e13feb4fd65e881bf65dfa40a53c6b89a061f19c4136b`,
matching `stage2-provenance.receipt`
(`authority=explicit-full-bootstrap-stage2-trust-root`). A single isolated
focused compile of `perf_facts.spl` was attempted. The candidate reported the
same locationless `Unknown(0)` parser error for all 35 closure modules, including
unchanged dependencies, then failed closed. This is Stage 2 compatibility evidence
only; it neither validates nor rejects this branch. The command is not retried.

## Impact

Focused compiler checks, optimizer-plugin analysis, semantic differential tests,
and post-change performance measurements cannot produce accepted Stage 4 evidence
in this worktree. The admitted Stage 2 candidate is too old or incompatible to
provide actionable diagnostics for this source closure.

## Unblock condition

Deploy or link a provenance-recorded pure-Simple Stage 4 binary built for commit
`37bd406e219cc35cae049b4130f5167c21801864` (or rebuild this branch through the
documented minimal bootstrap composition), then run each planned focused check
once in isolated output/cache directories.
