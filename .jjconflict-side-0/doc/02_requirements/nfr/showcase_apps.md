# Showcase apps NFRs

- NFR-001: Deterministic initial frames and interaction results support semantic and pixel comparison.
- NFR-002: Surface startup or evidence failure returns a nonzero/typed failure; environmental skips are labeled `skipped`.
- NFR-003: Host and guest adapters reuse application render/state logic and differ only at the transport/presentation boundary.
- NFR-004: No new direct runtime bypasses; rendering goes through owning UI/Engine2D/browser facades.
- NFR-005: Focused tests cover every REQ and contain no placeholder passes or dummy implementations.
