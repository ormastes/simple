# Selected 2D, Skia and RenderDoc admission

Executable source: `test/03_system/app/ui/feature/simple_2d_skia_renderdoc_hardening_spec.spl`

Trace: REQ-2D-002, REQ-2D-003, REQ-2D-005, NFR-2D-001, NFR-2D-002.

## Scenario: fractional input with absent physical capture

1. **Load the pinned scene.** Hash a controlled quarter-pixel rectangle scene, build its shared `DrawIrComposition`, lower it to `UiIr`, and require that its `0.25` coordinate survives.
2. **Preflight the complete picture.** Require the optional Skia adapter to admit exactly one supported rectangle before any native work.
3. **Validate capture provenance.** Represent the absent physical Linux Vulkan capture with an explicit absent device, no selected resource, no completion tokens and no pixels.
4. **Compare canonical final pixels.** Require a nonpassing `left-blocked-environment` result. No synthetic pixels or event counts can turn this row into a pass.

This scenario checks the cross-module admission boundary. It does not qualify the optional provider, dual-backend rendering, or N2 physical-device evidence. Run it only when a current pure-Simple test runner is available; the existing binaries currently fail on unrelated parser paths before this scenario executes.
