<!-- codex-research -->
# Native module cache invalidation NFRs

- NFR-001: Zero stale-object acceptance across the mutation matrix.
- NFR-002: The authoritative complete-witness gate accepts zero stale objects
  across 1,000 representative cross-revision incremental actions.
- NFR-003: Warm no-change build reaches at least 99% object hits.
- NFR-004: An unrelated public-interface edit recompiles no unaffected sibling
  modules.
- NFR-005: Witness/key computation consumes less than 5% of warm build wall
  time on the representative compiler/tool closure.
- NFR-006: Body-only dependency edits preserve dependent hits when observable
  interface, resolution, referenced layout, provider, and configuration facts
  are unchanged.
- NFR-007: Signature/layout changes and newly preferred resolution candidates
  invalidate every affected direct consumer.
- NFR-008: Decision receipts include compiler SHA-256, target, mode, manifest,
  cache schema, action counts, decisions, mismatches, wall time, and max RSS.
