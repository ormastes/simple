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
- Accept matching guarded style-token edits, reject stale tokens, and prove the
  accepted token is visible in HTML classes and SDD export.
- Generate stable multi-node geometry signatures, accept guarded alignment, and
  reject stale selections, missing nodes, unsupported align modes, and invalid
  geometry.
- Accept guarded horizontal/vertical distribution for 3+ nodes and reject too
  small selections or unsupported distribution axes.
- Parse parent, auto-layout, gap, padding, and constraint metadata with
  legacy-safe defaults.
- Resolve horizontal and vertical frame auto-layout into deterministic absolute
  geometry and expose the resolved values through HTML and SDD export.
- Accept guarded parent, auto-layout, and constraint edits; reject stale nodes,
  missing parents, parent cycles, invalid layout modes, invalid constraints, and
  malformed integer gap/padding.

## System Coverage

- IDE Office plugin suite verifies the LLM catalog includes Designer, the UI
  editor owner module, UI editor label/layout/auto-layout/constraint/
  align/distribute/layer/style-token actions, and the read-only
  `ui-inspect-node` / `ui-style-token-read` actions.
