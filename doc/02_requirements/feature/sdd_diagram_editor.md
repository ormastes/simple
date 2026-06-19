# SDD Diagram Editor Requirements

## Scope

First production slice for the SDN-backed diagram editor dialect.

## Requirements

- SDD-001: The diagram dialect has a stable name, `SDD: Simple Diagram
  Document`, and preferred file extension `.sdd.sdn`.
- SDD-002: Diagram nodes preserve editable shape, x/y position, width/height,
  and layer metadata from dense SDN and canonical tables.
- SDD-003: Diagram connectors preserve editable route, waypoints, and start/end
  anchor metadata from dense SDN and canonical tables.
- SDD-004: HTML rendering exposes deterministic editor metadata for SDD
  diagrams, nodes, and connectors.
- SDD-005: Weave rules can apply node layout and shape edits by selector.

## Out of Scope

Interactive drag handles, draw.io XML import/export, and a full browser editor
are follow-up slices.
