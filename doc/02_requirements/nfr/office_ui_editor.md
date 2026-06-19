# Office UI Editor NFR

- NFR-UI-001: The substrate must be pure and run without GUI, browser, network,
  shell-out, or desktop APIs.
- NFR-UI-002: HTML output must escape node labels and metadata.
- NFR-UI-003: Geometry must be deterministic and text/i64-oriented to avoid the
  current f64 nested-struct blocker.
- NFR-UI-004: Feature-check metadata must remain stable for LLM/tool use.
