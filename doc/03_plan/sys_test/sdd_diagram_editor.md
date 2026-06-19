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

## Evidence

- Unit spec:
  `test/01_unit/editor/services/sdn_graph_diagram_spec.spl`
- Generated manual:
  `doc/06_spec/test/01_unit/editor/services/sdn_graph_diagram_spec.md`

## Follow-Up

Future system specs should cover interactive editor commands for create, move,
resize, connect, reroute, layer, and export once those commands exist.
