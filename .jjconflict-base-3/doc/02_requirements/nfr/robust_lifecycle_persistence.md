# Robust Lifecycle Persistence NFRs

- NFR-001: The core model shall be pure Simple and usable without raw `rt_*` access.
- NFR-002: Validation shall be deterministic and allocation-bounded by the supplied graph and registration sizes.
- NFR-003: Public names shall follow current snake_case function and PascalCase type conventions.
- NFR-004: Examples shall compile with current generic `<>`, constructor, enum qualification, `val`, and `if val` conventions.
- NFR-005: Invalid metadata shall fail closed with a typed validation result rather than a silent default.
- NFR-006: The initial implementation shall remain under 800 lines per file and avoid duplicate lifecycle models.
- NFR-007: Documentation shall distinguish implemented library behavior from future proof, storage, and platform work.

