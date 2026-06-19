# Office UI Editor Test Plan

## Unit Coverage

- Parse design name, canvas size, frames, components, layers, and component
  roles.
- Render deterministic HTML with `data-format="html-ui"` and stable node
  metadata.
- Serialize to SDD node tables.
- Accept matching guarded label edits and reject stale edits.

## System Coverage

- IDE Office plugin suite verifies the LLM catalog includes Designer, the UI
  editor owner module, and UI editor actions.
