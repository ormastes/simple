# GUI rendering evidence status

**Updated:** 2026-09-26  
**Status:** Incomplete for pairwise widget rendering and final pixel parity

The file `test/03_system/check/gui_widget_pairwise_rendering_impl_spec.spl` contains
30 sample matrix rows for 7 named widget types. Their six dimension-pair
categories contain **134 distinct pairs**. The earlier “831/831 pairs in 250
rendering tests” claim was a target calculation, not measured coverage. The
spec now counts unique pairs from actual rows and reports `incomplete` against
that historic 831-pair target. Duplicate rows do not increase the count.

The same spec projects one real button widget through
`common.ui.widget_draw_ir.widget_tree_to_draw_ir_cpu` and checks that a command
for the button is emitted. This establishes a narrow GUI-to-shared-DrawIR
witness. It does not execute a DrawIR backend, inspect final pixels, exercise
the matrix row's layout/system/device settings, or compare native Vulkan with
upstream Skia.

The old helper allocated a `SoftwareRenderer`, cleared it, and considered a
nonempty pixel buffer a widget-rendering pass. It never supplied the named
widget to that renderer. The old “bug detection” checks compared constants to
themselves. Those assertions were removed because they could pass with no
widget rendering at all.

## Evidence levels

| Evidence | Current state |
|---|---|
| Sample row inventory | 30 rows; 7 widget names |
| Distinct dimension pairs in those rows | 134, counted from row values |
| GUI widget to shared DrawIR | One button command witness in this spec; wider widget command coverage lives in `test/01_unit/lib/common/ui/widget_draw_ir_widgets_spec.spl` |
| Executed backend pixels for these rows | Unverified |
| Final pixel comparison with upstream Skia or Chrome | Unverified |
| Interaction events for these rows | Unverified |

Run the focused spec with a working pure Simple runtime:

```sh
bin/release/aarch64-apple-darwin-macho/simple test \
  test/03_system/check/gui_widget_pairwise_rendering_impl_spec.spl \
  --mode=interpreter --no-cover-check
```

The `--no-cover-check` flag is needed because this evidence status spec does
not claim 80% source branch coverage. On the 2026-09-26 local runtime, the
command exited 139 during test discovery before executing cases. That run is
**UNKNOWN**, not a PASS. Fixing the runner or using an admitted working pure
Simple binary is needed before promoting the focused spec verdict.

A complete pairwise rendering claim requires a generated array tied to the
current `WidgetKind` inventory, actual GUI widget construction for every row,
the row's layout/theme/viewport applied, final pixel readback, and a comparison
oracle with backend and frame provenance.
