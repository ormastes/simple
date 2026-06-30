<!-- codex-design -->
# Simple 3D Graph IR Detail Design

## Data Structures

- `GraphIr3DResource`: resource kind, handle id, and binding slot.
- `GraphIr3DPass`: color/depth attachment ids and draw range metadata.
- `GraphIr3DDraw`: pass id plus vertex/index/uniform/texture/pipeline ids and
  indexed draw parameters.
- `GraphIr3D`: mutable graph container with resource, pass, and draw arrays.

## Algorithms

- Recording dedupes resources on insertion.
- Optimization copies unique resources and rebuilds each pass with draws sorted
  by pipeline id, texture id, vertex buffer id, index buffer id, then uniform id.
- Replay walks passes in order, begins a backend render pass, binds draw state,
  issues `draw_indexed`, and ends the pass.
- Software backend replay uses Math3D point/direction transforms and assigns
  updated nested `ForwardRenderer3D` state back to the backend after drawing.

## Error Handling

Invalid meshes, invalid pipelines, and unknown pass ids are ignored during
recording. Replay assumes graph nodes were produced by the recorder or optimizer.
