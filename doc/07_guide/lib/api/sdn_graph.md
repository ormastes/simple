# SDD / SDN Graph Syntax

**SDD (Simple Diagram Document)** is the diagram dialect built on SDN. Preferred
files use `.sdd.sdn`. SDD graph blocks describe renderable graph structure with
compact node and edge syntax, canonical SDN tables, reusable CSS labels,
draw.io-style connector metadata, Figma-like geometry, and selector-based
weaving. The source syntax uses `@foo` for visual CSS names; the normalized
internal field is named `css`.

## Dense Graph

```sdn
graph: login_flow
direction: right
theme: modern
css_file: "./modern.css"

User: User @person
Auth: Auth Service @card @important
DB: Database @storage shape: cylinder
Panel: Settings @card shape: rounded x: 40 y: 80 width: 220 height: 120 layer: ui

User -> Auth: Login @primary
Auth -> DB: Query @db
Panel -> Auth: config route: orthogonal waypoints: 150x100;150x40 start: right end: left
Auth ~> Log: Event @async
UI -x DB: forbidden @violation
```

Rules:

- `@foo` attaches visual CSS/tag name `foo` to the current node or edge.
- `shape:`, `x:`, `y:`, `width:`, `height:`, and `layer:` attach diagram editor
  metadata to nodes.
- Edge metadata `route:`, `waypoints:`, `start:`, and `end:` attach connector
  path and anchor metadata.
- `css foo:` defines style, shape, or layout hints for `@foo`.
- `weave @:` injects `@foo` names into matching nodes or edges by selector.
- `css_file:` imports an external stylesheet for final SVG or HTML output.

## Canonical Tables

The dense graph above normalizes to SDN tables:

```sdn
nodes |id, label, css, role, shape, x, y, width, height, layer|
    User, User, person, actor, , , , , ,
    Auth, Auth Service, "card important", service, , , , , ,
    DB, Database, storage, database, cylinder, , , , ,
    Panel, Settings, card, , rounded, 40, 80, 220, 120, ui

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

    edge where kind = request:
        add: primary

    edge where kind = async:
        add: async dashed
```

After weaving, the graph is equivalent to:

```sdn
User: User role: actor @person
Auth: Auth Service role: service @card @service
DB: Database role: database @storage shape: cylinder

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
classes derived from `@name`.
