# SDD / SDN Graph Syntax

**SDD (Simple Diagram Document)** is the diagram dialect built on SDN. Preferred
files use `.sdd.sdn`. SDD graph blocks describe renderable graph structure with
compact node and edge syntax, canonical SDN tables, reusable CSS labels,
draw.io-style connector metadata and grouping, Figma-like geometry, and
selector-based weaving. The source syntax uses `@foo` for visual CSS names; the
normalized internal field is named `css`. Group/container membership uses the
canonical node field `parent`.

## Dense Graph

```sdn
graph: login_flow
direction: right
theme: modern
css_file: "./modern.css"
canvas: width: 1200 height: 800 grid: 16 snap: true zoom: 100 background: #ffffff

User: User @person
Auth: Auth Service @card @important
DB: Database @storage shape: cylinder
Panel: Settings @card shape: rounded x: 40 y: 80 width: 220 height: 120 layer: ui
Button: Save @primary shape: rounded x: 72 y: 120 width: 96 height: 32 layer: ui parent: Panel

User -> Auth: Login @primary
Auth -> DB: Query @db
Panel -> Auth: config route: orthogonal waypoints: 150x100;150x40 start: right end: left
Auth ~> Log: Event @async
UI -x DB: forbidden @violation
```

Rules:

- `@foo` attaches visual CSS/tag name `foo` to the current node or edge.
- `shape:`, `x:`, `y:`, `width:`, `height:`, `layer:`, and `parent:` attach
  diagram editor metadata to nodes. `parent` is the canonical source for
  draw.io-like group/container membership.
- Edge metadata `route:`, `waypoints:`, `start:`, and `end:` attach connector
  path and anchor metadata.
- `canvas:` attaches optional draw.io-like document canvas metadata: page
  width, page height, grid size, snap mode, zoom, and background. Canvas values
  are document state, not node state.
- `css foo:` defines style, shape, or layout hints for `@foo`.
- `weave @:` injects `@foo` names and selected layout/group fields into
  matching nodes or edges by selector.
- Pure edit APIs can update one node's shape/style metadata or one connector's
  route metadata without reparsing or touching unrelated graph entries.
- Multi-node layout APIs align or distribute selected nodes with a guarded
  geometry signature so stale editor selections fail closed.
- `css_file:` imports an external stylesheet for final SVG or HTML output.

## Canonical Tables

The dense graph above normalizes to SDN tables:

```sdn
graph: login_flow
direction: right
theme: modern
css_file: "./modern.css"
canvas: width: 1200 height: 800 grid: 16 snap: true zoom: 100 background: #ffffff

nodes |id, label, css, role, shape, x, y, width, height, layer, parent|
    User, User, person, actor, , , , , , ,
    Auth, Auth Service, "card important", service, , , , , , ,
    DB, Database, storage, database, cylinder, , , , , ,
    Panel, Settings, card, , rounded, 40, 80, 220, 120, ui,
    Button, Save, primary, , rounded, 72, 120, 96, 32, ui, Panel

edges |from, to, label, css, kind, route, waypoints, start_anchor, end_anchor|
    User, Auth, Login, primary, normal, , , ,
    Auth, DB, Query, db, normal, , , ,
    Panel, Auth, config, , normal, orthogonal, "150x100;150x40", right, left
    Auth, Log, Event, async, async, , , ,
    UI, DB, forbidden, violation, forbidden, , , ,
```

## CSS Definitions

Use `css name:` to define reusable style names.

```sdn
css card:
    fill: var(color.card)
    stroke: var(color.line)
    radius: var(radius.card)
    text: var(color.text)

css storage:
    extends: card
    shape: cylinder

css person:
    extends: card
    shape: person

css primary:
    target: edge
    stroke: var(color.primary)
    stroke_width: 2
```

Canonical style tables:

```sdn
css |name, extends, target|
    card, none, node
    storage, card, node
    person, card, node
    primary, none, edge

styles |css, key, value|
    card, fill, var(color.card)
    card, stroke, var(color.line)
    card, radius, var(radius.card)
    card, text, var(color.text)
    storage, shape, cylinder
    person, shape, person
    primary, stroke, var(color.primary)
    primary, stroke_width, 2
```

## Weaving

`weave @:` injects CSS labels into graph entities matched by selectors.

```sdn
graph: login_flow
direction: right
theme: modern
css_file: "./modern.css"

User: User role: actor
Auth: Auth Service role: service
DB: Database role: database

User -> Auth: Login kind: request
Auth -> DB: Query kind: query
Auth ~> Log: Event kind: async

weave @:
    node where role = actor:
        add: person

    node where role = service:
        add: card service

    node where role = database:
        add: storage
        shape: cylinder
        parent: DataLayer

    edge where kind = request:
        add: primary

    edge where kind = async:
        add: async dashed
```

After weaving, the graph is equivalent to:

```sdn
User: User role: actor @person
Auth: Auth Service role: service @card @service
DB: Database role: database @storage shape: cylinder parent: DataLayer

User -> Auth: Login kind: request @primary
Auth -> DB: Query kind: query
Auth ~> Log: Event kind: async @async @dashed
```

## Markdown Embedding

Markdown preview treats fenced `sdn-graph` and `graph` code blocks as renderable
graphs:

````markdown
```sdn-graph
graph: login_flow
User: User @person
User -> Auth: Login @primary
```
````

The TUI preview renders a compact graph summary. The GUI preview emits
deterministic HTML with `sdn-graph`, `sdn-graph-node`, and `sdn-graph-edge`
classes plus `sdd-diagram`, `sdd-node`, `sdd-connector`, `data-format="sdd"`,
geometry attributes, connector route/waypoint attributes, and `sdn-css-<name>`
classes derived from `@name`. Nodes also expose `data-parent` for group or
container membership. The root exposes optional canvas metadata as
`data-canvas-width`, `data-canvas-height`, `data-canvas-grid`,
`data-canvas-snap`, `data-canvas-zoom`, and `data-canvas-background`, and maps
canvas width/height to deterministic root style lengths when present.

## Rendered Connector Contract

SDD HTML includes an SVG `.sdd-connector-layer` overlay before node buttons.
Each rendered connector path has:

- `data-edge-index`: stable edge index in canonical graph order.
- `data-path`: the exact SVG path string used in `d`.
- `data-route`, `data-waypoints`, `data-start-anchor`, and `data-end-anchor`:
  editable routing metadata.

`route: simple` renders a straight `M x,y L x,y` path, with optional explicit
waypoints inserted as straight line segments. `route: orthogonal` renders
Manhattan-style segments through each waypoint: horizontal to waypoint x, then
vertical to waypoint y, then horizontal/vertical to the target anchor.

`sdn_graph_update_edge_at` is the pure reroute operation for editor event
wiring. It updates an edge's route, waypoint string, and anchors by index while
leaving node geometry and graph metadata untouched.
`sdn_graph_update_edge_label_at` updates only the visible connector label.
`sdn_graph_update_edge_style_at` updates only connector CSS labels.
`sdn_graph_update_edge_endpoints_at` reconnects a connector's source and target
node ids.

`sdn_graph_update_node_at` is the broad pure node edit operation for editor
event wiring. It updates one node's CSS labels, role, shape, x/y geometry,
width/height, and layer by index while leaving node id/label, connectors, CSS
definitions, styles, and graph metadata untouched. `sdn_graph_update_node_label_at`,
`sdn_graph_update_node_shape_at`, and `sdn_graph_update_node_style_at` are
narrow helpers for label-only, shape-only, and style-label-only actions.

`sdn_graph_update_node_parent_at` is the pure group/container edit operation. It
updates one node's `parent` field by index while preserving geometry, style,
shape, label, and connector metadata. The field is allowed to be empty for an
ungrouped node.

`sdn_graph_update_canvas` is the pure canvas/page edit operation. It updates
document-level width, height, grid, snap, zoom, and background metadata while
preserving all node, connector, CSS, and weave state.

`sdn_graph_duplicate_node_checked(graph, source_id, new_id, dx, dy)` copies one
node with a caller-provided unique id and integer x/y offset. It preserves the
node label, style, role, shape, size, layer, and parent metadata, and fails
closed with `invalid-id`, `duplicate-id`, `invalid-offset`,
`ambiguous-source`, `invalid-geometry`, or `missing-node`.

`sdn_graph_geometry_signature(graph, node_ids)` returns the stable
`id:x,y,width,height` signature for a selected node set in canonical graph
order. `sdn_graph_align_checked(graph, node_ids, expected_signature, mode)` and
`sdn_graph_distribute_checked(graph, node_ids, expected_signature, axis)` are
the draw.io-style multi-node layout operations. They return a
`SdnGraphEditResult` and fail closed with `stale-selection`, `missing-node`,
`invalid-selection`, `unsupported-align-mode`, `unsupported-distribute-axis`, or
`invalid-geometry` instead of partially mutating a graph. Supported align modes
are `left`, `center`, `right`, `top`, `middle`, and `bottom`; supported
distribution axes are `horizontal` and `vertical`.

## Selection And Inspection

Selection is a transient render projection, not model state. Use
`sdn_graph_render_html_with_selection(graph, selected_node_id,
selected_edge_index)` when an editor surface needs selected-node or
selected-connector metadata. The base `sdn_graph_render_html(graph)` keeps the
same signature and delegates to the unselected projection.

Selected renders add root `data-selected-node-id` and
`data-selected-edge-index` attributes. Nodes and connectors keep their existing
SDD metadata and additionally expose `data-selected`, `aria-selected`, and the
`sdd-selected` class when selected. Connector selection is index-based and uses
the existing `data-edge-index` canonical graph order.

Use `sdn_graph_inspect_node(graph, node_id)` and
`sdn_graph_inspect_edge(graph, edge_index)` for read-only editor sidebars.
Inspectors return deterministic found/missing snapshots without mutating the
graph. Edge inspection includes the computed SVG path when both endpoints can
be resolved.
