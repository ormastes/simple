# WM DrawIR retained idle switch — 2026-08-12

Status: mechanism PASS; end-to-end 8K/80 evidence pending.

The bare WM executor now retains the last successfully presented canonical
`DrawIrComposition` and one compact `u64` checksum per resolved content frame.
If the next frame has identical batch metadata, ordered commands, and image
checksums, it returns the retained scene revision without raster replay,
backend submission, framebuffer present, or pixel-buffer comparison. No
WebIR/GuiIR or transient texture/atlas state is introduced.

Changed batch metadata, commands, image ordering, or image checksums fail open
to the existing full composition-present path. The current multi-batch patch
carrier is therefore not used for unsafe partial replay; LOCAL damage remains
a separate next-stage integration.

Verification:

- `simple check src/os/compositor/engine2d_wm_frame_executor.spl`: PASS with a
  bounded 180-second compiler allowance.
- Optimizer: 70 advisory opportunities, estimated ~50%; no performance claim
  is derived from this estimate.
- The focused SPipe spec was updated with unchanged/command-change/image-change
  controls, but the shared test runner currently fails before examples on the
  unrelated parse error in `src/compiler/80.driver/driver_vhdl_artifacts.spl`.
- A seed-only direct fixture also hit the existing `invalid field receiver`
  runtime defect and was not retained as evidence.

This establishes the zero-work idle decision in production source. It does not
yet prove physical scanout, pixel parity after LOCAL damage, RSS, or measured
8K p50/p95. Those remain required before an 8K/80 WM admission.
