# Shared Multilingual GPU Fonts — TLDR

One canonical `FontRenderer` prepares generation-bound `FontRenderBatch`
material for GUI/Web through Draw IR and for Engine2D/Engine3D consumers.
Simple emits the shared atlas-composite programs; backend adapters own device
resources and may claim execution only after submission and device readback.

`font_types.spl` also owns the one immutable `FontRenderConfig` and
`FontExecutionPolicy`. `Suggested(auto)` uses the engine's executable adapter
order; a named target moves first, then remaining GPUs and CPU. `Preferred`
tries the named target then CPU; `Required` tries the named target only.
Compatibility entrypoints construct the documented default config and delegate.

WM/GUI/Web/2D resolution also stays under `FontRenderer`: Web layout consumes
`ResolvedFontMetrics` (stable candidate identity plus exact advances), Draw IR
carries handle-free semantic family/identity/advances and shaped glyph IDs,
positions, and logical clusters, and Engine2D verifies the same identity before
paint. Unstyled legacy commands remain bitmap-compatible.
SimpleOS reuses `FontAssetCandidate` and must stage pinned Noto Sans Mono bytes
through every existing image-builder path before guest WM startup. Its legacy
WM still needs frame-level Draw IR migration; byte staging is not that proof.

The pinned 10-language × 10-category policy currently proves 57 native cells:
54 no-feature identity cells, Noto Sans Devanagari for exact Hindi `hi`, and
Noto Sans Arabic for the exact Arabic/Urdu witnesses; `zh/mono` is the one
fallback to Noto Sans SC.
Other complex scripts, emoji sequences/color and the unexecuted single-`U+1F600` promotion, general GSUB/GPOS/BiDi, Engine3D native
execution, executed Web/GUI/WM glyph-pixel parity, retained SimpleOS guest
pixel evidence, and performance targets remain gated. Atlas and face generations invalidate cached material; unavailable
hardware or stale handles fail closed.
