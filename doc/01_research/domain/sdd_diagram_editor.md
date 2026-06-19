<!-- codex-research -->
# SDD Diagram Editor Domain Research

## Primary References

- draw.io connectors:
  https://www.drawio.com/docs/manual/connectors/
- draw.io connector waypoints:
  https://www.drawio.com/docs/manual/connectors/waypoints-connectors/
- Figma plugin API `layoutPositioning`:
  https://developers.figma.com/docs/plugins/api/properties/nodes-layoutpositioning/
- Figma auto layout:
  https://help.figma.com/hc/en-us/articles/360040451373-Guide-to-auto-layout
- Figma vector networks:
  https://help.figma.com/hc/en-us/articles/360040450213-Vector-networks
- Figma components:
  https://help.figma.com/hc/en-us/articles/360038662654-Guide-to-components-in-Figma

## Domain Features to Preserve

draw.io-level diagram editing centers on:

- shapes on a canvas;
- connectors as first-class edges;
- fixed and floating connector endpoints;
- route/path styles and waypoints for connector clarity;
- arrows, connector styles, and shape libraries;
- layers and multi-page organization.

Figma-level HTML editor behavior centers on:

- frames and reusable components;
- explicit `x`, `y`, `width`, and `height`;
- auto-layout frames for responsive arrangement;
- absolute-position children inside layout frames;
- vector-like shape layers with fills/strokes.

## SDD Mapping

The first SDD slice maps those concepts to repo-native SDN:

- SDD node = shape/frame/component candidate.
- SDD node `x/y/width/height` = Figma-like absolute geometry.
- SDD node `layer` = draw.io/Figma layer organization.
- SDD edge = connector.
- SDD edge `route/waypoints/start_anchor/end_anchor` = draw.io connector path
  and endpoint metadata.
- SDD `css` labels + `styles` = reusable visual style tokens.
- SDD `weave` = batch style/layout edits over matched nodes and edges.

## Requirement Direction

Continue with SDD as the canonical diagram file format instead of inventing a
separate non-SDN diagram syntax. Add editor commands around this model in small
verified slices: create, move, resize, connect, reroute, layer, and export.
