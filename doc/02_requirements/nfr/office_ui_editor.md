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
