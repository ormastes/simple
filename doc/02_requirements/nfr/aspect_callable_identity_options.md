<!-- codex-research -->
# NFR options: canonical callable identity and E-APACK008

## Target 1 — Balanced semantic index (recommended)

- Canonical index construction and reachability are O(F + E) time and memory.
- Expected identity lookup is O(1); no per-root graph rebuild, filesystem scan,
  or subprocess is permitted in compilation.
- Incremental invalidation is limited to the changed callable and
  reverse-reachable callers.
- On a fixed 10,000-function/50,000-edge fixture, incremental retained storage
  is <= 96 bytes/function + 24 bytes/edge above the existing HIR baseline.
- Runtime denial is O(1), performs zero I/O and allocation, and a resident cache
  hit adds at most one policy/phase branch.
- Report p50/p95 compile time and max RSS against the same baseline revision and
  runtime; any unmet target becomes a measured tracked blocker.

- Pros: explicit linear-complexity and memory guard with realistic room for a
  framed semantic identity.
- Cons: requires retained measurement fixtures and counters.
- Effort: M in addition to feature implementation.

## Target 2 — Compact semantic index

- All Target 1 correctness, complexity, invalidation, and runtime requirements.
- Incremental retained storage is <= 64 bytes/function + 16 bytes/edge.
- The 10,000-function/50,000-edge fixture must stay within 5% compile-time p95
  and 4 MiB peak-RSS increase over the pre-identity baseline.

- Pros: tighter compiler and cache footprint.
- Cons: likely requires identity interning/compaction and more optimization
  work before semantic wiring can land.
- Effort: L in addition to feature implementation.
