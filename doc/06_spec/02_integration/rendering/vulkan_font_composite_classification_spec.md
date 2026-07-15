# Vulkan Font Composite Conditional Execution

> Manual mirror of `test/02_integration/rendering/vulkan_font_composite_classification_spec.spl`.
> Automatic regeneration was attempted on 2026-07-13 but the current self-hosted
> compiler exited 139 while loading the new Vulkan extern surface.

## Prove native submission and device readback

Run the focused conditional scenario on the target host. It stops at the first
unavailable rung; absence is not converted into a pass.

1. Probe the real Vulkan runtime and initialize the canonical retained session.
2. Require session initialization to auto-install the hash-pinned precompiled
   three-buffer font composite SPIR-V; a missing pipeline stops as unavailable.
3. Reject CPU/other devices and hosts without fenced submission before font
   batch, atlas, or destination mutation.
4. On an accelerated device, submit one exact 1×1 white glyph batch into a 2×2 target.
5. Require full dispatch, a completed and destroyed real fence, stable selected
   device/type/driver identity, direct device readback, and exact packed-pixel CPU-oracle equality.
6. Require the absolute oracle checksum `-1242373024502763654`; matching unknown
   pixels alone is insufficient.

### Honest outcomes

| First unavailable rung | Required result |
|---|---|
| Vulkan runtime or session | `unavailable`, no device execution |
| CPU/other device | `accelerated-device-required`, never promoted |
| Fenced submission unsupported | `fenced-submit-required`, never promoted |
| Accelerated precompiled-SPIR-V pipeline | `promoted` only after fence, readback, and parity evidence |

<details>
<summary>Executable source</summary>

Source: `test/02_integration/rendering/vulkan_font_composite_classification_spec.spl`

</details>

## Status

The scenario and manual contract are current. This Linux worktree could not
execute or regenerate the scenario because the deployed self-hosted compiler
exits 139 on the newly added runtime extern surface. This is not native PASS
evidence and does not satisfy the separate Engine3D REQ-012/REQ-013 gate.
