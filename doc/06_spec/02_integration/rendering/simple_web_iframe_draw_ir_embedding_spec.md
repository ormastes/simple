# Simple Web iframe `srcdoc` through DrawIR

Status: RED until the focused qualified pure-Simple integration run is
available. The legacy iframe pixel path remains the parity oracle.

1. **Compose iframe srcdoc through Web semantics and Draw IR** — confirms the
   red marker at `(5,5)`, child green at `(20,20)`, and white outside at
   `(80,50)` through `DrawIrComposition -> Engine2D`.
2. **Preserve iframe paint order and ancestor clipping** — confirms child
   batches occur between parent segments, rebase to `(0,10)`, keep the common
   layer, prefix batch/surface/command/parent IDs, clear child hits, and clip
   a green child inside a 20x15 overflow ancestor while leaving its outside
   white.
3. **Bound nested iframe work and fail closed** — confirms a 40x30 nested
   orange child, the grey depth placeholder, and a structural grey placeholder
   for a fractional-opacity ancestor. The overlapping pre/placeholder/post
   fractional fixture keeps all three in one opacity batch and checks exact
   `#c3c3c3` placeholder and `#f7a1a1` post pixels, rejecting a second blend.
4. **Retire legacy iframe pixel blitting after parity** — asserts no child
   image/material/hit authority even with inert child script, external image,
   and input markup. An authored child red/green vertical pair
   proves its deterministic initial scroll is zero; no child input or scroll
   interaction is enabled. It does not claim caller migration before exact
   legacy-pixel parity.
