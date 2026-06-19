# Office UI Editor NFR

- NFR-UI-001: The substrate must be pure and run without GUI, browser, network,
  shell-out, or desktop APIs.
- NFR-UI-002: HTML output must escape node labels and metadata.
- NFR-UI-003: Geometry must be deterministic and text/i64-oriented to avoid the
  current f64 nested-struct blocker.
- NFR-UI-004: Feature-check metadata must remain stable for LLM/tool use.
- NFR-UI-005: Stacking order must be deterministic; numeric layer values map to
  rendered z-index values, while non-numeric layers fall back to document order.
- NFR-UI-006: Selection and inspector reads must be pure derived views; they
  must not mutate node data or introduce persisted selection state.
- NFR-UI-007: Style-token edits must remain token-based and deterministic; they
  must not introduce arbitrary CSS parsing or host rendering dependencies.
- NFR-UI-008: Multi-node alignment and distribution must be all-or-nothing:
  stale signatures, missing nodes, too-small selections, unsupported modes, or
  non-integer geometry leave the original design unchanged.
- NFR-UI-009: Auto-layout and constraint resolution must be pure, deterministic,
  integer-only, and independent of browser/CSS layout engines.
- NFR-UI-010: Parent/layout/constraint edits must be all-or-nothing:
  stale-node guards, missing parents, parent cycles, unsupported layout modes,
  unsupported constraints, invalid gap/padding, or non-integer geometry leave the
  original design unchanged.
