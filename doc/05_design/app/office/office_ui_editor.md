# Office UI Editor Design

## Model

`OfficeUiDesign` is a text-backed document with a name, canvas dimensions, and
positioned `OfficeUiNode` records. Nodes carry id, label, kind, css token,
geometry, layer, component role, parent id, auto-layout mode/gap/padding, and
horizontal/vertical constraint metadata. Empty parent means top-level.
`layout_mode` is `off`, `horizontal`, or `vertical`; constraints use
`left`/`right`/`center`/`stretch` or `top`/`bottom`/`center`/`stretch`.

## Rendering

`office_ui_design_render_html` emits a single relative `.office-ui-design`
surface with absolutely positioned `.office-ui-node` children. The output is
inspector-friendly: stable `data-format`, `data-id`, `data-kind`,
`data-layer`, `data-z-index`, `data-component`, `data-parent`,
`data-layout-mode`, `data-layout-gap`, `data-layout-padding`,
`data-constraint-h`, and `data-constraint-v` attributes are part of the
contract. Rendering uses the pure auto-layout resolver before emitting absolute
geometry so the HTML remains inspectable without a browser layout engine.

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

`office_ui_design_read_style_token` is the style-specific read path over the
same inspector snapshot. It exposes the node's current style token without
turning selection or inspection into persisted document state.

## SDD Bridge

`office_ui_design_to_sdd` serializes nodes to the SDD table shape already used
by `std.editor.services.sdn_graph`, preserving resolved geometry, layers,
parent ids, auto-layout metadata, and constraints. This keeps Draw-style
diagrams and UI design screens on one editable document substrate.

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

`office_ui_design_update_style_token_checked` updates the node `css` token with
the same expected-value guard. Accepted edits change the rendered
`office-ui-css-*` class and the SDD `css` column; stale or missing nodes return
the original design unchanged. The compatibility helper
`office_ui_design_update_css_checked` remains the lower-level implementation.

`office_ui_design_geometry_signature` returns a stable design-order signature
for selected node geometry. Multi-node operations use that signature as the
stale-edit guard so LLM/tool callers can reject changes against outdated
selection geometry before any node moves.

`office_ui_design_align_checked` aligns selected nodes to the selection bounding
box for `left`, `center`, `right`, `top`, `middle`, and `bottom`. It updates only
`x` and/or `y`, preserves node size/style/layer metadata, and rejects stale
selection signatures, missing nodes, unsupported modes, too-small selections, or
non-integer geometry.

`office_ui_design_distribute_checked` distributes three or more selected nodes
on the `horizontal` or `vertical` axis using integer geometry and design-order
selection traversal. Like alignment, it is all-or-nothing and returns the
original design for stale, missing, unsupported, or non-integer inputs.

`office_ui_design_resolve_auto_layout` is the deterministic Figma-like layout
step. Frame nodes with `layout_mode=horizontal` or `vertical` place direct child
nodes in document order inside the frame's integer padding box, separated by an
integer gap. Horizontal frames advance child `x`; vertical frames advance child
`y`. Cross-axis constraints resolve the other axis: `left`/`top` pins to the
padding edge, `right`/`bottom` pins to the far padding edge, `center` centers
within the padded span, and `stretch` expands the child across the padded span.
Invalid integer geometry, gap, or padding leaves the design unchanged.

`office_ui_design_update_auto_layout_checked`,
`office_ui_design_update_constraint_checked`, and
`office_ui_design_set_parent_checked` extend the guarded-edit contract to
layout metadata. Parent edits reject missing parents and parent cycles. Layout
edits reject unsupported modes or malformed gap/padding. Constraint edits reject
unsupported constraint tokens. `office_ui_design_auto_layout_signature` and
`office_ui_design_resolve_layout_checked` give LLM/tool callers a stale-layout
guard before materializing resolved geometry.
