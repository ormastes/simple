<!-- codex-architecture -->
# Viz canonical frame builder

## Decision

`std.viz.feature.frame_builder` owns only construction state and emits the canonical entity `CompositorFrame`, `RenderPass`, `DrawQuad`, and `SharedQuadState` types. `AggregatorEntry` and `DisplayCompositor` consume those objects directly.

The builder creates one identity/SrcOver shared-quad state for each appended quad and stores its resulting index in that canonical quad. The completed pass list determines the canonical root pass. Metadata remains the deterministic defaults from `CompositorFrame.empty()`.

Raw `i64` texture or surface identities are not valid canonical GPU/surface provenance. Texture construction accepts a nonempty `SharedImageMailbox`, and surface references accept only typed `SurfaceId` values. Open/nested passes, invalid geometry, opacity, or normalized `SkColor4f` channels, unknown render-pass references, and pass-ID exhaustion fail closed rather than publishing a partial frame. `build()` returns `Option<CompositorFrame>` so an open builder is explicit `nil`, never an ambiguous empty submission. Color admission keeps the canonical `[0,1]` RGBA contract and rejects NaN/infinite values before backend packing; it does not silently clamp or normalize caller data.

## Typed surface composition

`DrawQuadKind.Surface` is the sole canonical surface-dependency wire form. A
builder emits a Surface quad and the same ordered `SurfaceId` in
`CompositorFrame.referenced_surfaces`; the aggregator validates that the two
declarations correspond exactly. The registry record lives in the leaf entity
module `std.viz.entity.aggregator_entry`, so frame submission and the walker do
not form a feature-module import cycle.

The aggregator imports a referenced child as a pass DAG, dependency-first. It
allocates aggregate-local pass IDs, remaps every local `RenderPass` reference,
and replaces the parent Surface quad with a canonical RenderPass quad. The
parent quad's rect, visible rect, blending flag, and shared-quad-state index
remain unchanged; this preserves the parent transform, clipping, opacity, and
blend boundary. Child primitives are not flattened into the parent.

Malformed frames fail closed: duplicate, forward, self, or dangling pass IDs;
negative or out-of-range shared-quad-state indices; missing or mismatched
surface declarations; non-finite rectangles, transforms, metadata, quad
numeric fields, or shared-quad-state opacity; empty/inverted render-pass or
quad geometry; and out-of-range normalized colors all fail closed before any
renderer-facing pass is copied. Unavailable
children and surface cycles return `CompositorFrame.empty()` rather than partial
output.
The aggregate result clears `referenced_surfaces` because all accepted typed
surface edges have become in-frame RenderPass dependencies.

Each aggregate also owns a fixed admission budget: at most 32 active surface
edges, 128 unique imported surfaces, 256 output passes, 4,096 quads, and 4,096
shared-quad states.  A frame reserves its complete pass/quad/SQS cost before
recursing, so a child fanout cannot overrun a parent reservation.  Completed
child imports are memoized by full `SurfaceId`; repeated parent references
reuse the same rebased child root rather than duplicate its DAG.  Any quota
breach rejects the entire aggregate to `CompositorFrame.empty()`.

## Evidence

`test/01_unit/lib/viz/frame_builder_canonical_integration_spec.spl` exercises builder → `AggregatorEntry` → `DisplayCompositor` with a canonical frame. It is host-independent structure evidence, not GPU rendering evidence.

`test/01_unit/lib/viz/canonical_typed_surface_composition_spec.spl` covers
typed identity, recursive pass-DAG import, missing-child and cycle rejection,
direct-frame declaration mismatch rejection, and replacement-frame visibility.
The current result is bootstrap-seed diagnostic execution only; fresh
pure-Simple self-hosted execution remains required before release admission.
