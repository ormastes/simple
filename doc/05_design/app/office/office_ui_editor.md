# Office UI Editor Design

## Model

`OfficeUiDesign` is a text-backed document with a name, canvas dimensions, and
positioned `OfficeUiNode` records. Nodes carry id, label, kind, css token,
geometry, layer, and component role.

## Rendering

`office_ui_design_render_html` emits a single relative `.office-ui-design`
surface with absolutely positioned `.office-ui-node` children. The output is
inspector-friendly: stable `data-format`, `data-id`, `data-kind`,
`data-layer`, `data-z-index`, and `data-component` attributes are part of the
contract.

`layer` is dual-purpose by design. Non-numeric values such as `base` and
`controls` remain semantic layer names and render with document-order fallback
z-index values. Numeric layer values render directly as deterministic CSS
`z-index` values for Figma-like stack ordering.

`office_ui_design_render_html_with_selection` is a compatibility extension over
the renderer. It adds root `data-selected-node-id`, per-node
`data-selected`/`aria-selected`, and the `office-ui-selected` class for the
selected node. Selection is intentionally not stored on `OfficeUiDesign`.

`office_ui_design_inspect_node` returns an `OfficeUiInspector` snapshot for a
node id, including label, kind, css token, geometry, layer, component role, and
resolved z-index. Missing nodes return `found=false` with reason
`missing-node`; successful reads return reason `selected`.

## SDD Bridge

`office_ui_design_to_sdd` serializes nodes to the SDD table shape already used
by `std.editor.services.sdn_graph`, preserving geometry and layers. This keeps
Draw-style diagrams and UI design screens on one editable document substrate.

## Editing

`office_ui_design_update_label_checked` mirrors the suite's guarded edit style:
updates apply only when the expected label matches the current label.

`office_ui_design_update_layout_checked` is the first Figma-like manipulation
operation. It moves/resizes a node only when the caller's expected
x/y/width/height tuple matches the current node geometry, then returns a new
design plus a compact diff. Stale geometry and missing nodes return rejected
`OfficeUiEditResult` values without mutating the original design.

`office_ui_design_update_layer_checked` updates semantic or numeric layer
metadata with the same stale-check contract. Numeric replacements immediately
affect rendered `data-z-index` and CSS `z-index`.
