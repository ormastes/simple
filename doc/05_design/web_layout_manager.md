# Web layout manager detail design

## Concrete interface

- `StyleDifference`: exact eight-way change classification.
- `WebLayoutStyleFingerprint`: hashes for inherited, paint, composite, intrinsic, self-layout, subtree-layout, formatting-context, and geometry state.
- `WebLayoutNodeSnapshot`: structural id, arena index, preserved DOM route, hierarchy/profile facts, computed-style fingerprint, resolved text metrics, CPU oracle box, and work metadata.
- `WebLayoutSnapshot`: DOM generation, viewport fingerprint, node projection, dependencies, execution profile, and fixed-point cap.
- `WebLayoutChange`: explicit style, insertion, font-resource, or viewport mutation plus its affected ids.
- `WebLayoutFrontier`: stable `WebLayoutDirtyNode` entries with per-node bits and an explicit fault.
- `WebLayoutRunResult`: generation, checked layout epoch, framework snapshot, epoch-qualified hit regions, stale flag, and fault.
- `WebLayoutSnapshotAdapter` and `WebLayoutManager`: concrete state holders; behavior is implemented without factories.

## Rules

Arena index `i` becomes structural id `i + 1`; parent `-1` becomes `0`, while `dom_route_id` is preserved separately. `display:none` and `contents` are admitted as block-owned non-rendering/flattened nodes; table family values map to table; grid, flex, inline/inline-block, and block/list-item/root are explicit. Absolute/sticky, scrolling overflow, and replaced elements form boundaries. `overflow_hidden` is clipping, not scrolling or containment. Unknown display values and compound replaced+absolute/sticky nodes are rejected before execution.

Fingerprint comparison is strongest-first: formatting-context, subtree layout, self layout, intrinsic, composite, paint, inherited, then no change. Intrinsic changes add line boxes and intrinsic ancestors. Insertions add inserted ids, the parent context, and downstream siblings. Font and viewport changes carry their exact geometry ids. Stable first occurrence wins during deduplication and each id retains its own dirty bits.

The manager rejects a request whose generation differs from its admitted generation. A successful run increments the epoch once and exposes the framework receipt unchanged. Maximum epoch reports `epoch-exhausted`; it never saturates.
