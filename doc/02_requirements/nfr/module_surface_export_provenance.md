# Module Surface Export Provenance NFRs

- **NFR-001 Determinism:** identical sources and aliases produce byte-stable
  owner selection and diagnostics independent of dictionary iteration order.
- **NFR-002 Memory:** provenance adds no executable bodies and no duplicate
  direct declaration records. Stage 4 peak RSS may increase by at most 5%.
- **NFR-003 Performance:** export finalization is bounded by export graph size;
  consumer lookup is O(1) average. Stage 4 HIR time may increase by at most 5%
  and should decrease for facade-heavy closures.
- **NFR-004 Safety:** cycle handling uses explicit visited state, not a silent
  depth-only cutoff. Ambiguity fails closed.
- **NFR-005 Diagnostics:** unresolved-export errors name the facade spelling,
  requested export, and canonical candidate path when available.
- **NFR-006 Compatibility:** Linux, macOS, Windows path separators, FreeBSD, and
  repository symlink spellings retain one canonical physical owner.
- **NFR-007 Observability:** debug mode reports provenance-map entries, cycle or
  ambiguity counts, fallback count, finalization time, and retained entry count.
- **NFR-008 Verification:** focused exact and adjacent tests pass once; Stage 4
  diagnostic fan-out is compared before/after without accepting new unresolved
  symbol/type families.
