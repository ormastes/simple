# DrawIR-v3 production owner bridge

Status: partial prototype / HOLD (2026-08-12)

The local GUI, Web, and WM Engine2D paths now attempt the same bounded
generation owner after producing the canonical `DrawIrComposition`:

```text
DrawIrComposition
  -> draw_ir_v2_to_v3
  -> fixed DrawIrPackedGenerationStoreV3
  -> seal + publish
  -> engine2d_draw_ir_v3_take_and_render
  -> generation/hash receipt
```

`draw_ir_packed_composition_owner_v3.spl` owns the bridge. It reserves one
fixed slot and one queue entry, writes the complete identity rows, and aborts
the unpublished slot on any write, seal, or publication refusal. The store
rejects zero-capacity queues and exposes `abort` only for `ENCODING` or
`SEALED` generations; publication changes `SEALED` to `QUEUED`, `take()` alone
changes `QUEUED` to `IN_FLIGHT`, and an `IN_FLIGHT` generation can be released
only by the Engine2D owner’s completion path.

The initial production subset is intentionally fail-closed for v3 commands:
rectangles render through the packed owner. Text, images, groups, and other
commands remain on the existing canonical `DrawIrComposition` executor, so
Engine2D’s transient `FontRenderer`/`FontRenderBatch` material remains the
sole vector-font path. No atlas, cache, device handle, or backend command
buffer is added to Draw IR.

The receipt binds acceptance to `arena_id`, monotonic `generation`, content
hash, rendered command count, and storage release. The WM path uses the
bridge; GUI/Web call sites remain provisional and require hosted-path evidence
before this can be considered production-integrated.

## Frozen identity handoff (2026-08-12)

The Vulkan showcase host's identity path now creates one
`DrawIrPackedIdentitySnapshotV3` before the packed generation is exposed as
`IN_FLIGHT`. The snapshot owns value-semantic copies of the exact canonical
`draw_ir_to_sdn` composition text, its SHA-256, and the ordered projected v3
rows. The packed hash preimage is exactly
`draw-ir-packed-v3|arena=<arena>|generation=<generation>|rows=<count>|<row>;...`;
it binds arena, generation, row count, and ordered rows. `slot` is not part of
that hash: it is validated separately against the submission and authoritative
store state.

Immediately before commit, `engine2d_packed_v3_finalize_identity` revalidates
the authoritative `IN_FLIGHT` store rows/hash/state, reserializes the current
composition, recomputes its digest and projected rows, and checks the copied
submission. Store mutation, snapshot/submission mismatch, row reordering, or
an ABA/replayed handoff poisons the owner; a rejected GPU/font receipt also
poisons the exact in-flight generation rather than completing it. A post-take
identity mismatch during preparation follows the same poison path.
`engine2d_packed_v3_identity_artifact` recomputes hashes from its copied fields
before emitting the raw `packed.identity` observation. The shell adapter then
recomputes composition bytes/hash and the exact packed preimage independently,
rejecting missing, malformed, duplicate, or surplus row records, so
`backend.env` is not an authority for either hash.

The corresponding raw artifact is an observation contract and is not GPU or
compiled-Simple evidence. Fixture bundles remain explicitly
`CONTRACT_ONLY`; no hardware, native compiler, or production rendering PASS
is implied by this identity gate.

GROUP, IMAGE, and TEXT commands are currently honest refusals; canonical
batches are not yet flattened count-first. The WM refusal fallback and RECT
semantic rejection are implemented. Hosted Web production integration is not
yet proven, and the bridge still allocates the adapted v3 scene and performs
text hashing/copying during admission; the allocation-free active-generation
requirement remains unmet. No production PASS should be inferred from these
prototype tests.

Focused coverage is in:

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_packed_owner_v3_spec.spl`
- `test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl`
