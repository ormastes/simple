# SDD Diagram Editor Test Plan

## Requirements

- SDD-001: The SDN diagram dialect has a stable name, SDD: Simple Diagram
  Document, and preferred `.sdd.sdn` extension.
- SDD-002: Diagram nodes preserve shape, explicit x/y position, width/height,
  and layer metadata.
- SDD-003: Diagram connectors preserve route, waypoints, and start/end anchors.
- SDD-006: Diagram connectors render deterministic SVG `data-path` values from
  anchors and waypoints.
- SDD-007: Pure reroute edits update edge route, waypoint, and anchor metadata.
- SDD-008: Pure node edits update shape, style labels, role, geometry, and
  layer metadata while preserving non-target nodes and connector metadata.
- SDD-009: Parent/container membership is parsed from dense syntax and canonical
  tables, rendered as deterministic HTML metadata, canonicalized, and editable
  through a pure parent update helper.
- SDD-010: Selected node and connector rendering adds deterministic
  `data-selected` / `aria-selected` metadata while preserving existing SDD
  geometry and connector attributes.
- SDD-011: Node and connector inspectors return pure found/missing snapshots
  with geometry, grouping, route, waypoint, anchor, and computed path metadata.

## Evidence

- Unit spec:
  `test/01_unit/editor/services/sdn_graph_diagram_spec.spl`
- Generated manual:
  `doc/06_spec/test/01_unit/editor/services/sdn_graph_diagram_spec.md`

## Follow-Up

Future system specs should cover interactive editor commands for create, move,
resize, connect, reroute, layer, and export once those commands exist.
