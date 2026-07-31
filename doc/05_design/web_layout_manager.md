# Web layout manager detail design

## Concrete interface

- `StyleDifference`: exact eight-way change classification.
- `WebLayoutStyleFingerprint`: hashes for inherited, paint, composite, intrinsic, self-layout, subtree-layout, formatting-context, and geometry state.
- `WebLayoutNodeSnapshot`: structural id, arena index, preserved DOM route, hierarchy/profile facts, computed-style fingerprint, resolved text metrics, CPU oracle box, and work metadata.
- `WebLayoutSnapshot`: DOM generation, viewport fingerprint, node projection, family-aware text requests/results, dependencies, execution profile, and fixed-point cap.
- `WebLayoutChange`: explicit style, insertion, font-resource, or viewport mutation plus its affected ids.
- `WebLayoutFrontier`: stable `WebLayoutDirtyNode` entries with per-node bits and an explicit fault.
- `WebLayoutRunResult`: generation, checked layout epoch, framework snapshot, epoch-qualified hit regions and `HitRegionOf` mappings, stale flag, and fault.
- `WebLayoutSnapshotAdapter` and `WebLayoutManager`: concrete state holders; behavior is implemented without factories.

## Rules

Arena index `i` becomes structural id `i + 1`; parent `-1` becomes `0`, while `dom_route_id` is preserved separately. `display:none` and `contents` are admitted as block-owned non-rendering/flattened nodes; table family values map to table; grid, flex, inline/inline-block, and block/list-item/root are explicit. Absolute/sticky, scrolling overflow, and replaced elements form boundaries. `overflow_hidden` is clipping, not scrolling or containment. Unknown display values and compound replaced+absolute/sticky nodes are rejected before execution.

Fingerprint comparison is strongest-first: formatting-context, subtree layout, self layout, intrinsic, composite, paint, inherited, then no change. Intrinsic changes add line boxes and intrinsic ancestors. Insertions add inserted ids, the parent context, and downstream siblings. Font and viewport changes carry their exact geometry ids. Stable first occurrence wins during deduplication and each id retains its own dirty bits.

The manager rejects a request whose generation differs from its admitted generation. A successful run increments the epoch once and exposes the framework boxes, fragments, line boxes, overflow, execution proof, and receipt unchanged. Maximum epoch reports `epoch-exhausted`; it never saturates. Viewport changes invalidate only ids whose post-restyle geometry fingerprints changed.

The production render session supplies `BrowserRenderSnapshot.document_generation`, creates or resets its retained manager on generation changes, and performs the first full framework run after the CPU oracle exists. Retained snapshots compare geometry fingerprints to form stable incremental frontiers; paint-only frames do not call the manager or increment its epoch. Adapter faults enter the manager through `WebLayoutFrontier.fault` and remain observable; they are never discarded to preserve the visual return type.

Large homogeneous candidates use the browser CUDA `LayoutExecutionPort`. Only typed semantic values are uploaded; oracle boxes remain host-side. The first admitted slice is positive fixed-pixel, childless block/flex/grid roots with no box-model extras. Unsupported shapes pre-reject and execute through the CPU oracle port.
