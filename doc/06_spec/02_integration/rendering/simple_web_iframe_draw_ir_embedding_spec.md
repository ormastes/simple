# Simple Web iframe `srcdoc` through DrawIR

Status: RED until the focused qualified pure-Simple integration run is
available. The legacy iframe pixel path remains the parity oracle.

1. **Compose iframe srcdoc through Web semantics and Draw IR** — confirms the
   red marker at `(5,5)`, child green at `(20,20)`, and white outside at
   `(80,50)` through `DrawIrComposition -> Engine2D`.
2. **Preserve iframe paint order and ancestor clipping** — confirms child
   batches occur between parent segments and child commands retain present,
   bounded clips.
3. **Bound nested iframe work and fail closed** — confirms a 40x30 nested
   orange child and the grey depth placeholder.
4. **Retire legacy iframe pixel blitting after parity** — asserts no child
   image/material/hit authority and zero child scroll; it does not claim caller
   migration before exact legacy-pixel parity.
