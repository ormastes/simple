# Engine2D Compositor.add_layer insertion-sort double-decrement

Status: Open.

Date: 2026-07-20

## Context

`src/lib/gc_async_mut/gpu/engine2d/compositor.spl` `Compositor.add_layer`
maintains an ascending `z_order` sort via insertion sort:

```
me add_layer(layer: Layer):
    self.layers.push(layer)
    var i = self.layers.len() - 1
    while i > 0:
        if self.layers[i].z_order < self.layers[i - 1].z_order:
            val tmp = self.layers[i]
            self.layers[i] = self.layers[i - 1]
            self.layers[i - 1] = tmp
            i = i - 1        # (A) inside the if-branch
        else:
            return
        i = i - 1            # (B) unconditional, every loop iteration
```

`i` is decremented twice per swap: once inside the `if` branch (A) and once
more unconditionally at the bottom of the loop body (B). A correct insertion
sort must decrement exactly once per swap so the newly-placed element is
compared against its new left neighbor. This implementation skips that
comparison, so the bubbled element can land one slot too early and never gets
compared against the element that was originally two slots to its left.

## Impact

Inserting 3+ layers where a low-`z_order` layer is added *after* two
already-correctly-ordered higher layers produces an incorrectly sorted
`layers` array — a middle layer ends up with the wrong relative position.
Because `composite_to_buffer` draws strictly in array order (index 0 first,
last index visually on top for opaque pixels), an incorrect array order means
a lower-`z_order` layer can render **on top of** a higher-`z_order` layer
wherever they overlap — the exact "topmost wins" compositing contract the
class docstring promises is violated.

The bug is invisible with only 2 layers (a single comparison is always
sufficient) and invisible when the layer that ends up in the wrong slot
doesn't visually overlap anything at the tested point — which is presumably
why it has shipped unnoticed.

## Reproduction (traced by hand, confirmed conceptually against the source)

Insert three layers via `add_layer`, in this order:
- `A`, `z_order = 2`
- `B`, `z_order = 3`
- `C`, `z_order = 1`

Expected sorted result (ascending `z_order`): `[C(1), A(2), B(3)]`.

Trace:
1. `add_layer(A)`: `layers = [A(2)]`.
2. `add_layer(B)`: `i=1`; `B(3) < A(2)`? No → `else: return`. `layers = [A(2), B(3)]` (correct).
3. `add_layer(C)`: `i=2`; `layers[2]=C(1) < layers[1]=B(3)`? Yes → swap →
   `layers = [A(2), C(1), B(3)]`; `i` becomes `1` (A) then `0` (B); loop
   condition `i > 0` is now false, loop exits **before comparing `C` against
   `A`**.

Final array: `[A(2), C(1), B(3))]` — **wrong**. `C` (z_order=1) should be
first; instead `A` (z_order=2) is first and `C` sits behind it in the array
at index 1.

Consequence for `composite_to_buffer`: at any pixel covered by both `A` and
`C` (but not `B`), draw order is `A` then `C`, so `C` (the lower z_order,
opaque) paints over `A` last and wins the pixel — inverted from the documented
"z_order controls draw order (lower first)" / higher-z-on-top contract.

## Test coverage added (this pass, audit-only — no source fix)

`test/01_unit/lib/gpu/engine2d/compositor_layer_zorder_spec.spl` — the `it`
block `"XFAIL bug engine2d_compositor_add_layer_insertion_sort_double_decrement:
three out-of-order insertions break topmost-wins"` asserts the *correct*
expected pixel (the higher-z_order layer's color) at the A/C overlap point.
Against current source this assertion does not hold (see the file's `main()`
runtime probe evidence in
`test/01_unit/lib/gpu/engine2d/probe_layer_overlap_hit_test.spl`, key
`three_layer_topmost_pixel_matches_expected`, which prints `false`/mismatched
values under current source). This is intentional: the spec documents the
contract, not the bug, per project convention for honest xfails.

## Required fix

Remove the extra unconditional decrement at (B) — decrement `i` only once,
inside the `if` branch after a swap (or restructure the loop to decrement
exactly once per iteration regardless of branch, i.e. move a single `i = i -
1` so it always executes exactly once per swap and zero times on `return`).
Not applied in this pass — audit findings feed a separate fix lane per
mission scope (do not modify engine source in the audit pass).
