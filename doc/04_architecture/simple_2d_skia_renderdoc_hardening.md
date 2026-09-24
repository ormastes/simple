<!-- codex-design -->
# Hardening architecture — selected C/N2 extension

Status: C/N2 selected by the user on 2026-09-26. Implementation and physical Linux Vulkan admission remain open. Existing accepted backend-equivalence architecture remains authoritative.

## Shared boundary

The selected upstream plan is `doc/03_plan/ui/unified_surface_draw_ir_and_html_css_conformance.md`: direct 2D, GUI and Web producers emit `DrawIrComposition`, lowered by `draw_ir_to_ui_ir` into packed `UiIr`, with Vulkan first. Preserve this selected boundary. An optional upstream-Skia adapter consumes the admitted shared semantic/execution contract without adding another public IR. Web owns computed style/layout/stacking/shaping; GUI owns widget state and damage; neither owns a duplicate raster IR. An explicit evidence capsule consumes completed backend records outside ordinary rendering.

| Owner | Existing boundary / agreed proposal | Responsibility |
|---|---|---|
| Shared IR | DrawIR v3 fractional payload and explicit affine v4 transport implemented; runtime unverified | One versioned migration of fractional geometry, affine state and raster policy |
| Shared lowering | `draw_ir_to_ui_ir` carries f64 rectangles and v4 matrix/policy into UiIr v2; runtime unverified | Preserve the matrix and policy, or reject atomically before execution |
| 2D compatibility | `skia_render_picture_on_engine2d_reported`; proposed `skia_picture_engine2d_preflight`, `skia_render_picture_on_engine2d_strict` | Preflight full picture, reject loss, preserve preview receipt |
| Native provider | Existing GPU owner; selected backend ID `upstream-skia-ganesh-vulkan` | Opaque handles, enabled Vulkan features, thread/device lifetime and synchronization |
| Web | Existing browser_engine producer | CSS/layout/paint source IDs, pinned asset/interaction state |
| GUI | Existing UI/Engine2D producer | Widget state and identical geometry through shared contract |
| Capture | `BackendRenderRecord`, `BackendRenderReadback`, `BackendExecutionProvenance` | Completed resource identity, decoded pixels and provenance |
| v1 diagnostics | `RdocEventSet`, `rdoc_events_parse`, `rdoc_diff` | Validate event evidence, label command alignment diagnostic |

Use adapter composition for optional upstream consumption and the existing virtual evidence capsule for cross-cutting capture. Do not weave readback/subprocesses into ordinary frames. The default embedded profile does not link upstream Skia.

## Correctness boundaries

Strict mode validates the whole picture before engine allocation or drawing. Preview may render a subset only with `complete=false`, nonempty reason and loss/skip accounting. Capabilities distinguish API declaration, device support, implemented operations and verified operations.

Cross-renderer verdict compares final canonical pixels after input/frame/provenance validation. Same-renderer event alignment remains diagnostic. Existing record equivalence compares richer command semantics; add an explicit visual projection rather than silently changing accepted record equality.

Native provider owns device/queue/context until all dependent resources and work retire. Exported handles carry identity/generation; no raw pointers in SDN. Flush, submit and completed readback are separate states. Device loss, ambiguous target selection and incomplete frame terminate admission with typed errors.

## Existing producer interface names

Retain `simple_2d_to_draw_ir` (planned direct-2D adapter), `widget_tree_to_draw_ir` (GUI), `simple_web_layout_render_html_draw_ir` (Web), and `draw_ir_to_ui_ir` (shared lowering) from the existing selected plan. Reuse existing implementations where present; these names do not certify current implementation status. Coordinate with `doc/03_plan/agent_tasks/unified_surface_draw_ir_and_html_css_conformance.md` before shared-IR edits.

## Case 02 affine extension boundary

DrawIR v4 adds optional `DrawIrAffine2D(a,b,c,d,tx,ty)` and an explicit
per-command raster policy. The local f64 rectangle remains authoritative;
the matrix maps its local `(x,y)` to surface `(a*x+c*y+tx,b*x+d*y+ty)`.
Clips are surface-space rectangles and are applied before the command-local
matrix. V3 bytes and integer compatibility remain unchanged. Older consumers
reject v4 or affine commands before submission; `draw_ir_to_ui_ir` preserves
matrix, clip and policy atomically. CPU source provenance is distinct from an
admitted GPU execution target; adapters may rewrap only after full preflight.

The v4 data contract, SDN checked parser, UiIr v2 lowering, and audited
legacy-consumer rejection gates are present in source. Their focused specs
have static review only: the current macOS Simple runners cannot provide a
trustworthy execution result. This does not admit case 02 or a GPU backend.

The Web owner resolves CSS transform order/origin and the complete paint
inventory. Engine2D owns a candidate real Vulkan affine coverage path, not
host emulation or integer rectangle shader fallback. The optional Skia owner
has a private v3 record and CPU validator; native v3 drawing is still
disabled. Private v1/v2 records remain immutable. Both
owners validate matrix finiteness, transformed bounds, clip space, coverage
policy, color/alpha domain and target completion before a paired receipt.
The evidence capsule compares independently decoded final pixels and device
UUID provenance; event labels remain diagnostic.
