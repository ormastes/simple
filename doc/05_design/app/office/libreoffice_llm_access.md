# LibreOffice LLM Access Design

## Contract

`app.office.llm_catalog` provides:

- `office_llm_feature_catalog()` -> structured rows for Markdown, Writer, Calc,
  Impress, Draw, Designer, Base, Math, Mail, Planner, and Counter.
- `office_llm_catalog_summary()` -> compact line for IDE feature checks.
- `office_llm_catalog_app_names()` -> stable app ordering for LLM prompts,
  manuals, and tests.
- Writer and Impress rows advertise Markdown-source actions:
  `render-writer-markdown-html`, `writer-markdown-summary`, and
  `render-ppt-markdown-html`.

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
