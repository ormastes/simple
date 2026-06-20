# LibreOffice LLM Access Design

## Contract

`app.office.llm_catalog` provides:

- `office_llm_feature_catalog()` -> structured rows for Markdown, Writer, Calc,
  Impress, Draw, Designer, Base, Math, Mail, Planner, and Counter.
- `office_llm_catalog_summary()` -> compact line for IDE feature checks.
- `office_llm_catalog_app_names()` -> stable app ordering for LLM prompts,
  manuals, and tests.
- Writer and Impress rows advertise Markdown-source actions:
  `render-writer-markdown-html`, `writer-markdown-summary`,
  `writer-markdown-stats`, `writer-markdown-search`,
  `writer-markdown-range`, `writer-markdown-replace`, `writer-markdown-insert`,
  `writer-markdown-delete`, `writer-markdown-outline`,
  `render-ppt-markdown-html`, and
  `ppt-markdown-outline`.
- Base rows advertise table read/query/edit actions including
  `base-table-summary`, `query-table`, `render-base-table-html`, and `db-edit`.
- Draw rows advertise SDD-backed read/edit actions including
  `sdd-document-summary`, `render-sdd-html-with-selection`,
  `edit-sdd-node-style`, `sdd-node-style-read`, `sdd-node-geometry-read`,
  `edit-sdd-edge-label`, `sdd-edge-label-read`, `sdd-edge-label-point-read`, `edit-sdd-edge-style`,
  `sdd-edge-style-read`, `edit-sdd-edge-kind`, `sdd-edge-kind-read`,
  `sdd-edge-route-read`, `sdd-edge-path-read`,
  `sdd-edge-segments-read`, `sdd-edge-endpoints-read`, `inspect-sdd-node`,
  and `inspect-sdd-edge`.

## Constraints

- Pure metadata only: no GUI, browser, network, shell, filesystem, or host calls.
- Owner modules point at existing implementations; the catalog must not duplicate
  renderer/editor logic.
- Feature-check output remains width-bounded and parity-stable between TUI and
  GUI modes.
- Markdown is the product source format for Writer and Impress; HTML is the
  generated render target.

## Verification

The IDE office system spec asserts app count, owner modules, feature/action
coverage, summary count, and report parity. Generated manuals are refreshed via
SPipe docgen after spec changes.
