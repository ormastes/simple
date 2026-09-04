# Frozen Package Compilation — TLDR

- Every compile quietly freezes source into an immutable, leased SCV revision
  under ignored `build/scv/` **before** discovery.
- Automatic integration is read-only toward Git/user SCV state: no commits,
  pushes, index/ref/history/lock changes, user-file writes, or timestamp touches.
- After admission, all source and generated-input reads use the frozen snapshot;
  live-worktree fallback is forbidden.
- A persistent SCV-revision/variant-bound package catalog replaces recursive
  source-tree scans and duplicate CLI/driver closure walkers.
- `PackageTldrV1` supplies concise graph/action identities;
  `PackageSummarySmfV1` supplies indexed exports/types/ABI, direct imports,
  reverse facts, initializer/provider needs, sources, generated inputs, and
  toolchain/options evidence.
- Raw content digest is separate from export/ABI, initializer, provider, and
  implementation digests. Comment-only edits may reparse the producer but do not
  invalidate dependents when semantic dimensions are unchanged.
- Import cycles compile as deterministic SCC actions. Independent SCCs run in
  bounded parallel workers and the parent commits results canonically.
- Snapshots, summaries, archives, catalogs, leases, receipts, recovery, and GC
  are atomic and confined to `build/scv/`.
- Git/SCV/editor events refresh internal inventory quietly; overflow/cold state
  uses explicit receipt-bearing reconciliation, never a hidden full scan.
- Clean warm builds open zero source files and target ≤25% of current entry-
  closure wall time; private/comment edits target ≤35% with exact access receipts.
