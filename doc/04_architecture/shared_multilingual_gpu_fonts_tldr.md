# Shared Multilingual GPU Fonts — TLDR

One canonical `FontRenderer` prepares generation-bound `FontRenderBatch`
material for GUI/Web through Draw IR and for Engine2D/Engine3D consumers.
Simple emits the shared atlas-composite programs; backend adapters own device
resources and may claim execution only after submission and device readback.

WM/GUI/Web/2D resolution also stays under `FontRenderer`: Web layout consumes
`ResolvedFontMetrics` (stable candidate identity plus exact advances), Draw IR
carries only semantic family/identity/advances, and Engine2D verifies the same
identity before paint. Unstyled legacy commands remain bitmap-compatible.
SimpleOS reuses `FontAssetCandidate` and must stage pinned Noto Sans Mono bytes
through every existing image-builder path before guest WM startup.

The pinned 10-language × 10-category policy currently proves 54 native
no-feature Latin/Han/Cyrillic cells and one `zh/mono` fallback to Noto Sans SC.
Complex scripts, emoji shaping, GSUB/GPOS/BiDi completion, Engine3D native
execution, resolved Web layout/paint identity, SimpleOS image packaging, and
performance targets remain gated. Atlas and face generations invalidate cached material; unavailable
hardware or stale handles fail closed.
