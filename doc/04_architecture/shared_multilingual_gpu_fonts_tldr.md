# Shared Multilingual GPU Fonts — TLDR

One canonical `FontRenderer` prepares generation-bound `FontRenderBatch`
material for GUI/Web through Draw IR and for Engine2D/Engine3D consumers.
Simple emits the shared atlas-composite programs; backend adapters own device
resources and may claim execution only after submission and device readback.
The shared batch gate rejects unknown atlas-composite program versions and
noncanonical transforms before either engine mutates native state.
Portable GPU admission is two-phase: requested targets first compile and
validate semantics-compatible candidates with tool/validator provenance, then
independent review and exact reproduction may mark tracked pins verified.

`font_types.spl` also owns the one immutable `FontRenderConfig` and
`FontExecutionPolicy`. `Suggested(auto)` uses the engine's executable adapter
order; a named target moves first, then remaining GPUs and CPU. `Preferred`
tries the named target then CPU; `Required` tries the named target only.
Compatibility entrypoints construct the documented default config and delegate.
Native-sensitive Engine2D/Engine3D paths fill plans through
`font_execution_plan_into`, retain renderers in the shared one-slot owner, and
stage batch/projection data through caller-owned storage.

Vulkan font faults use one neutral scalar `FontOwnerFaultReceipt` contract.
Each 2D/3D owner retains monotonic masks and sequences and exposes only scalar
facades; calling the shared reason classifier does not prove an owner event.
Engine3D replaces atlas textures transactionally and retires the old native
texture only after the fresh upload succeeds, avoiding failed-replacement
identity corruption and resource growth.

WM/GUI/Web/2D resolution also stays under `FontRenderer`: Web layout consumes
`ResolvedFontMetrics` (stable candidate identity plus exact advances), Draw IR
carries handle-free semantic family/identity/advances and shaped glyph IDs,
positions, and logical clusters, and Engine2D verifies the same identity before
paint. `WebIR` remains the existing semantic/layout model, never a second draw
IR or a carrier for atlas/device material. Host Web executes its WebIR Draw IR;
`ui.browser` executes one canonical widget composition and does not fabricate
queue dispatch evidence. Unstyled
legacy commands remain bitmap-compatible.
SimpleOS reuses the full selected `FontAssetCandidate` catalog and is configured
to stage every pinned face through each existing image-builder path before guest
WM startup; this is a source/staging contract, not retained guest proof.
Desktop bootstrap attempts each long VFS path, then its FAT32 8.3 fallback,
attempts to register every readable face before render-target creation, and reports
whether the whole catalog was admitted without making partial registration
transactional. Its canonical
desktop executes `SharedWmScene -> DrawIrComposition -> DrawIrRenderTarget`
through `Engine2dWmFrameExecutor`. Hosted x86/ARM targets use Engine2D; RV64
uses `Riscv64DrawIrRenderTarget` over `Engine2DBaremetalCore` and the canonical
staged `FontRenderer` batch. `compositor_render.spl` owns the hosted Web loop
and stays outside the freestanding compositor closure. Canonical ARM64/x86_64
runner/readiness targets select that entry. Direct legacy `wm_entry.spl` files
remain compatibility-only.
On x86_64 and ARM64 registration of the selected catalog is attempted before
that frame and the existing `taskbar-clock` DrawIR slot is the witness; its
56x48 QEMU hash remains unset until retained capture evidence exists.
Hosted color-background frames now lower through the same Draw IR/Engine2D
route with one persistent raster session. Compatibility frames are labeled as
direct-framebuffer fallback and cannot satisfy live Engine2D evidence; source
routing is not runtime proof. SimpleOS rejects a frame when any typed selected-
font command was skipped, while explicit image degradation remains separate.

The pinned 10-language × 10-category source policy contains 67 native cells,
4 explicit script-sans mono fallbacks, 26 not-designed cells, and 3 unavailable
serif complex-script cells. It accepts sans Hindi and Arabic/Urdu witnesses plus
the exact monochrome Noto Emoji `U+1F600` corpus tuple for every selected
language tag; the last promoted-baseline self-hosted shaping/material scenario
exited 0. The refreshed scenario with pending serif probes has no admitted
runner PASS: pinned release SHA `04a38e21…` exits 139 before assertions, while
the latest retained candidate reaches a separate recursion guard.
Other complex scripts and emoji sequences/color remain policy exclusions.
REQ-016 moves general GSUB/GPOS into the existing parser/layout owners with
composed contextual remaps and one pixel/design-unit-aware variation context;
the selected high-level complex-script preprocessor still fails closed while
full BiDi, Engine3D native execution, executed Web/GUI/WM glyph-pixel parity, retained SimpleOS guest
pixel evidence, retained native v5 stage/promotion evidence, and performance targets remain gated. Transient Vulkan evidence owns fused queue/device, fence observation, readback, and CPU-oracle timings; durable records never make captured handles reusable authority. Atlas and face generations invalidate cached material; unavailable
hardware or stale handles fail closed.
