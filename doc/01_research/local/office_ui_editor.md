# Office UI Editor Local Research

## Scope

The office suite already has Markdown-source Writer/PPT rendering and an SDD
diagram substrate. The remaining editor gap is a pure, testable HTML design
surface for positioned frames/components that can later back GUI editing without
depending on browser or desktop APIs in feature checks.

## Existing Surfaces

- `src/app/office/md_wysiwyg.spl` owns Markdown source plus guarded edits.
- `src/app/office/word/html_render.spl` renders Writer Markdown to document
  HTML.
- `src/app/office/slides/html_render.spl` renders PPT Markdown and positioned
  slide object HTML.
- `src/lib/editor/services/sdn_graph.spl` owns SDD diagram metadata, geometry,
  connectors, and deterministic HTML.
- `src/app/office/llm_catalog.spl` is the IDE-visible LLM feature catalog.

## Finding

The suite had no dedicated UI design document model. Adding a pure
`app.office.ui_editor` model lets agents and IDE checks reason about UI frames,
components, layout, SDD export, and stale-safe edits without host GUI state.
