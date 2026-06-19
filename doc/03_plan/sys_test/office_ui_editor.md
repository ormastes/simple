# Office UI Editor Test Plan

## Unit Coverage

- Parse design name, canvas size, frames, components, layers, and component
  roles.
- Render deterministic HTML with `data-format="html-ui"` and stable node
  metadata.
- Serialize to SDD node tables.
- Accept matching guarded label edits and reject stale edits.
- Accept matching guarded move/resize layout edits and reject stale geometry.
- Render numeric layer values as z-index metadata and guard layer updates.
- Render transient selected-node state and expose read-only inspector metadata
  for found and missing nodes.

## System Coverage

- IDE Office plugin suite verifies the LLM catalog includes Designer, the UI
  editor owner module, UI editor label/layout/layer actions, and the read-only
  `ui-inspect-node` action.
