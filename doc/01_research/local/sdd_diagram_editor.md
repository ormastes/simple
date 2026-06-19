<!-- codex-research -->
# SDD Diagram Editor Local Research

## Scope

Research the current SDN-backed diagram support used inside Markdown docs and
the IDE preview, then identify the first implementation slice toward a
draw.io/Figma-level diagram editor.

## Current Implementation

- Parser/render owner: `src/lib/editor/services/sdn_graph.spl`.
- Markdown GUI embedding: `src/lib/editor/70.backend/gui_backend.spl` renders
  fenced `sdn_graph` blocks via `sdn_graph_render_html`.
- Existing guide: `doc/07_guide/lib/api/sdn_graph.md`.
- Glossary entry: `doc/glossary.md` currently defines generic SDN but not the
  diagram dialect.
- ASCII rendering: `src/lib/editor/services/sdn_graph_ascii.spl`.

## Findings

- Existing graph blocks were relationship-first: node id/label/css/role/shape,
  edge from/to/label/css/kind, CSS definitions, and weave rules.
- Rendering auto-positioned nodes on a percentage grid, so an editor could not
  preserve explicit Figma-like positions or draw.io-like layout edits.
- Connectors had kind/style but no route, waypoints, or anchor metadata.
- Shape changes existed only as `shape`, and weave could set shape but not
  position, size, or layer.

## Implemented First Slice

Name the SDN diagram dialect **SDD: Simple Diagram Document** with preferred
file extension `.sdd.sdn`.

Extend `sdn_graph` while preserving old syntax:

- Node geometry: `x`, `y`, `width`, `height`.
- Node organization: `layer`.
- Connector routing metadata: `route`, `waypoints`, `start_anchor`,
  `end_anchor`.
- HTML render metadata: `sdd-diagram`, `sdd-node`, `sdd-connector`,
  `data-format="sdd"`, and deterministic geometry attributes.
- Weaving can apply layout and shape edits to matched nodes.

## Remaining Work

- Multi-page diagrams and page-level canvas metadata.
- Shape libraries and reusable components.
- Connector endpoint validation against shape anchors.
- Interactive editor commands for move/resize/connect/reroute.
- Export/import compatibility with draw.io XML remains future work.
