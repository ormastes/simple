# SDD Diagram Editor Test Plan

## Requirements

- SDD-001: The SDN diagram dialect has a stable name, SDD: Simple Diagram
  Document, and preferred `.sdd.sdn` extension.
- SDD-002: Diagram nodes preserve shape, explicit x/y position, width/height,
  and layer metadata.
- SDD-003: Diagram connectors preserve route, waypoints, and start/end anchors.
- SDD-004: HTML rendering exposes deterministic editor metadata for SDD
  diagrams, nodes, and connectors.
- SDD-005: Weave rules can apply node layout and shape edits by selector.
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
- SDD-012: Canvas/page metadata is parsed from dense SDN, rendered as
  deterministic HTML root metadata, canonicalized, and editable through a pure
  canvas update helper.

## Evidence

- Unit spec:
  `test/01_unit/editor/services/sdn_graph_diagram_spec.spl`
- Generated manual:
  `doc/06_spec/test/01_unit/editor/services/sdn_graph_diagram_spec.md`
- IDE system spec:
  `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`
- IDE generated manual:
  `doc/06_spec/test/03_system/app/ide/feature/ide_office_plugin_suite_spec.md`

## Follow-Up

Current IDE system coverage exercises SDD render/export, node create, geometry
resize/move, connect, reroute, layer, delete, and metadata readback through the
headless Office action dispatcher. Add a narrower feature-owned
`sdd_diagram_editor` system spec only when this coverage needs to move out of
the IDE Office suite.
