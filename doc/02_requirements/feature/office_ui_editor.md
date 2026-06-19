# Office UI Editor Requirements

## Functional Requirements

- REQ-UI-001: Provide a named HTML UI design document substrate for Office.
- REQ-UI-002: Parse positioned frame/component records from text source.
- REQ-UI-003: Render inspector-ready HTML with stable format, node, layer, and
  component metadata.
- REQ-UI-004: Export design nodes to SDD-compatible node tables so Draw and UI
  editing share one diagram substrate.
- REQ-UI-005: Guard label edits with expected-value checks and stale rejection.
- REQ-UI-006: Expose the UI editor through the Office LLM catalog.
- REQ-UI-007: Guard node layout edits with expected x/y/width/height checks so
  move and resize operations reject stale geometry.
- REQ-UI-008: Support deterministic layer/z-order metadata for positioned nodes
  with guarded layer updates.
- REQ-UI-009: Support transient node selection rendering and read-only
  inspector snapshots without persisting selection into the design document.
- REQ-UI-010: Support guarded style-token edits so component visual classes can
  change with stale-token rejection and deterministic render/SDD output.

## Out of Scope

Live browser editing, collaborative cursors, constraints solving, and native
Figma import are future slices.
