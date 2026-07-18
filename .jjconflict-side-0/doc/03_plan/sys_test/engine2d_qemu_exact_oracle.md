<!-- codex-plan -->
# Engine2D QEMU Exact-Oracle Test Plan

## Status

**RED / execution blocked by TODO548.** TODO529 remains open. Current main has
one strict x86_64 spec row and a legacy
`test/09_baselines/engine2d_in_qemu/verification_scene.ppm`, but no independently
admitted oracle. The legacy fixture has no acceptable provenance for this gate
and must not be promoted as TODO529 evidence. Canonical AArch64 and RV64
production entries exist, but the executable spec has no rows for them. No live
result is claimed by this plan.

## Contract

The system gate covers REQ-016, REQ-017, and REQ-018 from
`simple_2d_renderdoc_backend_equivalence`. Each required architecture must:

1. Build a guest-native Engine2D verification entry with its architecture
   owner, linker script, target triple, QEMU machine, and display device.
2. Boot through the shared QEMU harness, render before readiness, and emit the
   row-specific post-present marker listed below.
3. Capture through `os.compositor.qemu_capture`, decode with the Simple PPM
   owner, and compare through `compare_exact`.
4. Require positive nonblack pixels, matching dimensions, and zero mismatches
   against that row's independently produced and reviewed oracle.
5. Emit and validate the complete
   `SimpleOsRenderTargetEvidence` contract: runtime/architecture/board and
   firmware identity; boot transport; display controller, driver, scanout, and
   resource IDs; DMA/cache/IOMMU mode; dimensions, stride, and format; positive
   surface handle and present sequence; completion; guest readback origin and
   pixel hash; serial and capture paths/hashes/tool; boot/frame correlation;
   oracle hash and zero mismatches.
6. Retain the ELF hash, serial log, QMP capture, oracle, validated evidence
   record, nonblack count, and exact mismatch count.

| Row | Required target and post-present marker | Current status |
|---|---|---|
| x86_64 | `get_wm_simple_web_check_target()`, standard VGA, `[desktop-gui] desktop-ready` | Migration from the minimal x86 fixture, compiler, and oracle blocked |
| AArch64 | `get_arm64_desktop_engine2d_target()`, RAMFB, `[desktop-gui-arm64] desktop-ready revision=` | Live exact-oracle evidence missing |
| RV64 | `scenario_target(scenario_by_name_direct("riscv64-display-smoke"))`, VirtIO-GPU, `SIMPLEOS_RISCV_DISPLAY_SMOKE_READY` | Live exact-oracle evidence missing |

REQ-018 also names SoC identity, fence evidence, an explicit guest receipt, and
capture-tool version. The current canonical struct does not expose those four
fields. Add them at the evidence owner, or obtain an approved requirements
clarification, before claiming complete REQ-018 coverage; the test must not
synthesize missing evidence.

## Shared SSpec Interface

- Target constructor: `_engine2d_targets() -> [OsTarget]`.
- Steps: `Build the dedicated SimpleOS Engine2D entry`, `Require the host QEMU target`, `Wait for the guest's rendered-frame serial marker`, `Capture the matching framebuffer through pure-Simple QMP`, and `Compare every capture pixel with the fixed independent oracle`.
- Helpers: `_nonblack` and `_oracle`; reuse shared QEMU/QMP/PPM owners for all
  other behavior.
- Replace the current `_engine2d_target()` minimal-x86 constructor with these
  canonical production target owners; do not keep two competing target paths.
- Any unavailable required target, missing oracle, capture error, dimension
  mismatch, or pixel mismatch must call `fail(...)`; no placeholder pass.

## Oracle Admission

Each architecture has a distinct oracle path because viewport and display
contracts differ. Every oracle must be captured or generated independently of
the guest scene implementation, reviewed by a person or
normal/highest-capability reviewer, and committed with provenance and SHA-256.
The test never writes or refreshes it. Tolerance, auto-baseline, inline Python,
direct `rt_*`, cached-pass promotion, and CPU/fixture painting labeled as guest
output are forbidden.

## Verification Order

1. Static review: canonical imports, three real target entries, no forbidden
   shortcuts, current generated manual, and zero `.spl` files in `doc/06_spec`.
2. Once TODO548 supplies a valid compiler, run this spec once on a host with all
   three QEMU systems.
3. Independently review retained provenance and exact-pixel results before
   changing TODO529 from open.

Do not rerun a passing row in the same session. Stop after three fix/verify
cycles and report the remaining failure.
