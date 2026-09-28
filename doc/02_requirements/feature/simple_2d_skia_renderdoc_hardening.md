<!-- codex-research -->
# Simple 2D, Skia and RenderDoc hardening requirements

Selected by the user on 2026-09-26: feature option **C**. This is an incremental extension of the previously selected `DrawIrComposition -> draw_ir_to_ui_ir -> UiIr` producer model, with Vulkan first. The web layout engine and GUI widget model retain their own responsibilities; all raster routes consume one shared drawing contract.

| ID | Requirement | Acceptance evidence |
|---|---|---|
| REQ-2D-001 | Preflight a complete Skia picture before the Engine2D bridge emits any command. Reject unsupported or lossy geometry, paint, image and state semantics with the operation index and reason. Strict rendering and pixel readback fail closed on fallback, incomplete output or unknown readback source. | Focused bridge rejection and success scenarios. |
| REQ-2D-002 | Evolve the shared DrawIR with a versioned fractional geometry representation. Migrate admitted direct 2D, GUI and Web producers, serializers, and rendering consumers together, preserving existing integer input compatibility without silent rounding. | Round trip and fractional rendering tests across producer and consumer boundaries. |
| REQ-2D-003 | Compare completed final output through explicit resource identity, subresource, dimensions, stride, pixel format, alpha, color space, origin and crop metadata. Decode to canonical RGBA bytes before visual comparison. Report incomplete or ambiguous output as failure or blocked evidence. | Same-pixel/different-event and different-pixel/same-event scenarios; malformed metadata tests. |
| REQ-2D-004 | Keep RenderDoc event alignment diagnostic. Validate event schema and digest integrity, and distinguish event differences from a cross-renderer pixel verdict. | Parser and comparison regression scenarios. |
| REQ-2D-005 | Add an optional upstream Skia Ganesh Vulkan provider at a pinned upstream revision. It consumes the shared drawing contract and is excluded from default embedded linkage. It owns Vulkan context, queue, resource and thread lifetime; unsupported operations, device loss and unfinished work fail closed. | Build and lifetime contract tests plus admitted device capture. |
| REQ-2D-006 | Exercise direct 2D, Web and GUI scenes through both admitted Vulkan backends. Pin source assets and provenance, preserve web computed layout and GUI widget state, and record input as well as visible pixel evidence. | Executable corpus scenarios and completed per-backend receipts. |

The supplied 48-case HTML/CSS corpus is source material, not an admitted Vulkan golden. Neither equal event counts nor encoded PNG hashes establish visual equivalence. No second public web drawing IR, silent software fallback, or fabricated device receipt is allowed.
