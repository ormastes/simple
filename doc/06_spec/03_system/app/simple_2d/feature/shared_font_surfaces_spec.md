# Shared Font Material Across 2D and 3D Specification

> **Manual draft — pending canonical `spipe-docgen`.** This review copy mirrors
> the current executable SSpec while the pure-Simple compiler build is in
> progress. It is not generated-run evidence and does not claim a PASS.

Executable source:
`test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl`

## Scope

This scenario prepares one persistent CPU-owned glyph batch, verifies warm
atlas reuse, feeds the Engine2D atlas-subrect compositor, and exercises the
Engine3D HUD/world CPU compatibility entrypoints. It does not prove a native
GPU texture upload, submission, fence, readback, or presentation.

Requirements: partial REQ-006, REQ-009, and REQ-011 CPU/shared-material
evidence. This scenario intentionally does not claim REQ-008, REQ-012, or the
native NFR gates.

## Operator flow

### Prepare one shared font batch for 2D and 3D

1. Run the executable SSpec with the self-hosted pure-Simple runtime once it is
   available.
2. Observe the visible step: **Prepare one shared font batch for 2D and 3D**.
3. Verify all four examples execute without skips or pending placeholders.
4. Treat the output as CPU compatibility evidence only.

## Expected evidence

### Stable shared batch and warm reuse

- `FontRenderer.prepare_text("AB", …, 16)` produces two valid glyph quads.
- Atlas dimensions are 1024 × 1024 with 1,048,576 `u32` white-alpha pixels
  (4 MiB).
- The cold batch reports two dirty rectangles.
- Repeating the same glyphs reports zero dirty rectangles.
- Atlas generation and the first glyph atlas location remain stable.
- Quad byte offsets remain `0` and `1`.

### Engine2D consumer

- The shared white-alpha atlas subrectangle is tinted through
  `engine2d_font_atlas_subrect_pixels`.
- Output size equals the glyph quad area.
- At least one resulting pixel is nonzero.

### Engine3D compatibility surface

- A 64 × 64 Engine3D instance is explicitly created with backend `cpu`.
- HUD text and projected world text both report success.
- The backend remains `cpu` and the readback contains nonzero pixels.

### Fail-closed boundaries

- Font sizes `0` and `513` produce invalid batches.
- Empty content at size `16` is valid but empty.

<details>
<summary>Folded executable detail</summary>

The SSpec uses the real `FontRenderer`, Engine2D atlas-subrect helper, and
Engine3D CPU entrypoints. Setup and repeated structural assertions are folded
behind `setup_shared_font_fixture` and `expect_shared_font_batch`. Consult the
executable source for exact matcher calls.

</details>

## Claim boundary

The current scenario is a CPU oracle and API-compatibility check. Native 2D/3D
GPU proof requires the separate resource-handle, submission, fence, and
device-readback scenario; this manual does not substitute for it.
