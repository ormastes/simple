<!-- codex-design -->
# Stage4 re-export resolver: domain note

This is an internal compiler graph-resolution problem; no external protocol or
user-facing standard governs its semantics. The applicable design principle is
standard memoized graph traversal: cache completed answers by an immutable
graph identity, keep the active set scoped to one DFS path, and invalidate all
completed answers when the graph identity changes. Local compiler lifecycle
evidence is authoritative for this change.
