# LibreOffice LLM Access Research

## Scope

Research the existing IDE and LibreOffice-like app surfaces so an LLM can inspect
available apps, features, edit commands, owner modules, and evidence without
opening each implementation file.

## Existing App Feature Inventory

| App | Owner | Features |
| --- | --- | --- |
| Markdown | `app.office.md_wysiwyg` | line-by-line source, styled preview, guarded `md-edit`, stale rejection |
| Writer | `app.office.word.html_render` | Markdown source generates paper/document HTML; rich document block rendering remains a compatibility adapter |
| Calc | `app.office.sheets` | cells, ranges, formulas, guarded `sheet-edit`, stale/malformed source rejection |
| Impress | `app.office.slides` | Markdown source generates slide-deck HTML; slide object rendering remains a compatibility adapter; outline, CSS-like design metadata, guarded `slide-edit` |
| Draw | `common.drawing.vector_shapes` | integer vector shapes, SVG output, labels, canvas validation |
| Base | `app.office.base_db` | in-memory text tables, insert/select/project, deterministic route validation |
| Math | `app.office.math_editor` | MathML token rendering, superscript, square root |
| Counter | `app.office.counter` | deterministic increment/decrement/reset, unsupported-action rejection |

## LLM Access Findings

- The IDE feature check already gives human-readable capability checks, but it
  does not expose a complete per-app feature/action/evidence catalog.
- `app.office.libreoffice` knows the six LibreOffice branded apps but not
  Markdown or Counter edit surfaces.
- `src/app/ide/feature_report.spl` is the right product surface because it is
  pure Simple metadata/probes and runs in both TUI and GUI feature-check modes.
- Writer and Impress should be treated as Markdown-authored apps that generate
  HTML for rendering. Direct rich-text or slide-object HTML renderers are
  compatibility paths, not the preferred product source format.

## Implementation Direction

Add a pure metadata catalog under `app.office` with one row per app. Each row
must include app name, component key, owner module, feature list, LLM actions,
and evidence key. The IDE feature report should expose a concise summary plus
the app names; tests should inspect the structured rows for full detail.
