# Physical Vulkan 2D controlled clip qualification

This is the next Stage 1 primitive slice for REQ-2D-005, REQ-2D-006,
NFR-2D-002, and NFR-2D-003. It does not qualify the 48 Web pages or a full
GUI widget scene.

## Pinned source and independent oracle

- Fixture: `test/fixtures/simple_2d_skia/controlled_clipped_rect_v2.sdn`
- Source SHA-256: `b16d53f7785a09559bf209797fcb724906f896b93d23eff512bda69ec44d8f2f`
- Canonical 16 × 16 RGBA SHA-256: `0664e46ad7f384f9b594b7d1c1e8d0db13a197846a4527db5c152258baf20dc0`
- Required commands: opaque full-target clear, oversized clipped draw,
  zero-width clip, disjoint clip, then an unclipped draw. The last draw
  detects clip state carried into later commands.

The source loader parses all five commands. The analytic oracle constructs
expected pixels independently of that loader. Engine2D computes the exact
integer visible intersection before Vulkan dispatch; Skia v2 applies a
per-command aliased clip with balanced canvas state.

## Physical run

On a Linux machine with an integrated or discrete Vulkan device, first build
the pinned optional Skia provider and the native qualification worker as in
`physical_vulkan_2d_controlled_rectangle.md`. Use a fresh output name:

```sh
sh scripts/check/check-vulkan-2d-qualification.shs \
  "$PWD/build/optional/vulkan_2d_qualification" \
  "$PWD/build/optional/libsimple_upstream_skia_ganesh_vulkan.so" \
  build/test-artifacts/vulkan_2d/controlled_clip_001 clip
```

`run-clip` starts isolated Engine2D and Skia worker processes. Each worker
must bind a completed native readback, selected-device UUIDs, fixture hash,
provider/build hash, and canonical RGBA. The orchestrator checks both bytes
against each other and the independent oracle. A successful controlled run
may write `scope: controlled-clipped-rectangle-only` in `run.sdn`. Imported
artifacts through `verify-clip` remain `candidate` even when their pixels
match, because a caller can construct those files.

## Open evidence

The pinned Skia checkout and physical Linux Vulkan device are absent from this
macOS workspace. The Simple spec runner is not trustworthy yet. No native
build, device-loss test, clipped-pixel capture, or physical `run-clip` PASS is
claimed. A passing primitive slice still leaves Web/GUI semantic scenes open.
