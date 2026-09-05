# SimpleOS server capability manifest NFRs

- NFR-SCM-001: Selection is bounded by a fixed owner-controlled protocol set.
- NFR-SCM-002: Missing, stale, empty, unsupported, or unknown evidence fails
  closed and cannot produce an advertised manifest.
- NFR-SCM-003: Capability projection adds no socket, parser, crypto, or protocol
  stack and therefore no independent cache or invalidation policy.
