# Shared Multilingual GPU Fonts — TLDR

One canonical `FontRenderer` prepares generation-bound `FontRenderBatch`
material for GUI/Web through Draw IR and for Engine2D/Engine3D consumers.
Simple emits the shared atlas-composite programs; backend adapters own device
resources and may claim execution only after submission and device readback.

The pinned 10-language × 10-category policy currently proves 54 native
no-feature Latin/Han/Cyrillic cells and one `zh/mono` fallback to Noto Sans SC.
Complex scripts, emoji shaping, GSUB/GPOS/BiDi completion, explicit Vulkan
fence/device identity, Engine3D native execution, and performance targets remain
gated. Atlas and face generations invalidate cached material; unavailable
hardware or stale handles fail closed.
