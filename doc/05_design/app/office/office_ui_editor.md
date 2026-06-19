# Office UI Editor Design

## Model

`OfficeUiDesign` is a text-backed document with a name, canvas dimensions, and
positioned `OfficeUiNode` records. Nodes carry id, label, kind, css token,
geometry, layer, and component role.

## Rendering

`office_ui_design_render_html` emits a single relative `.office-ui-design`
surface with absolutely positioned `.office-ui-node` children. The output is
inspector-friendly: stable `data-format`, `data-id`, `data-kind`,
`data-layer`, and `data-component` attributes are part of the contract.

## SDD Bridge

`office_ui_design_to_sdd` serializes nodes to the SDD table shape already used
by `std.editor.services.sdn_graph`, preserving geometry and layers. This keeps
Draw-style diagrams and UI design screens on one editable document substrate.

## Editing

`office_ui_design_update_label_checked` mirrors the suite's guarded edit style:
updates apply only when the expected label matches the current label.
