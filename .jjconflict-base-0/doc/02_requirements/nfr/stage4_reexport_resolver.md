<!-- codex-design -->
# Stage4 re-export resolver NFR

- NFR-001: the second identical lookup in a shared snapshot adds zero
  resolver graph traversals.
- NFR-002: cache invalidation is explicit at snapshot construction, not based
  on module count or filename heuristics.
- NFR-003: the full x86 Stage4 CLI build is the acceptance gate; no seed or
  cross-compiled result substitutes for it.
