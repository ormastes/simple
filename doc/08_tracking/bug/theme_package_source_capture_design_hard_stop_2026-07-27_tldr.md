# Theme package source-capture design hard stop — TLDR

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- Canonical `theme-package-install-wire-v1` text landed at `b1d0b3e27f`.
- No source-matched self-hosted runtime admits its aggregate ABI probe:
  Stage 4 still has receiver/module-key failures and a code-generation split
  blocker; the retained release binary predates the relevant sources.
- Source-capture design series `48fbcd1d91` through `50c886ca9b` is rejected
  and unintegrated after three cycles.
- A with-reader API cannot prove “no reader constructed” on cache hits; add a
  cache-owning production wrapper that constructs the reader only on misses.
- Strict missing-required-source rejection contradicts legacy missing-core
  empty-hash compatibility; requirements must select one transaction contract.
- Legacy aggregate loading remains independent.
- Native aggregate encoder/decoder use still needs the admitted incremental ABI
  probe.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
