# Layout Framework Local Research

## Goal

Identify the existing geometry oracle and the smallest reusable structural-compute surface needed by `layout_framework_plan.md`.

## Findings

- The parent contract is `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md` §§6, 9, 17, and 21.
- No source implementation currently exists under `src/lib/common/structural/`; DirtyMask, MappingKind/LayoutOf, StageReceipt, ExecutionProfile, layout snapshots, islands, profiles, and TextMeasurePort exist only as architecture pseudocode.
- The canonical browser CPU oracle is the flat-array pipeline in `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`: `LayoutResult`, `layout`, and `layout_with_style` own `bx/by/bw/bh`, wrapping, intrinsic widths, and document height.
- The older `layout.spl`/`layout_core.spl` BeLayoutBox pipeline lacks the grid/table/sticky/scroll coverage required by the plan and is not the adapter target.
- Existing text metrics enter layout through resolved font identity, advances, width, and line height; shaping is owned by `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` and the Skia shaper, so the framework must expose a port instead of approximating text.
- The browser oracle and font owner files are dirty in other active lanes; several browser layout/style files contain conflict markers. This lane must not edit them.

## Minimal Reuse Decision

Implement the required shared contracts in their structural owner modules, then keep the framework in `src/lib/common/structural/layout/`. Profiles delegate to one CPU-oracle boundary; they do not duplicate eight layout algorithms. Browser conversion remains a consumer adapter and must not be folded into common contracts.

## Risks

- `LayoutProfile` already names a responsive-UI type; use `LayoutProfileId`.
- `DependencyEdge` and `CostEstimate` exist in unrelated compiler scopes; do not root-export structural variants.
- Simple source uses `trait`, not architecture-pseudocode `interface`.

