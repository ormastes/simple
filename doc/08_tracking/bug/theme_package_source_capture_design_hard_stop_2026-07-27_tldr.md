# Theme package source-capture design hard stop — TLDR

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
