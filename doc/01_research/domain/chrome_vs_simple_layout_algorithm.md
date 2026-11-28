# Domain Research: Chrome Blink LayoutNG vs Simple Layout Algorithms

**Date:** 2026-11-28
**Worktree:** `/Users/ormastes/work/carbon_chrome_layout`
**Prior Local Reference:** `doc/01_research/domain/chromium_layoutng_parity_2026-06-11.md`

---

## 1. Blink LayoutNG Core Architectural Model

Chrome's Blink LayoutNG replaces legacy mutable, tree-walking layout with a strict two-phase, immutable constraint/fragment pipeline:

### 1.1 Immutable Inputs & Outputs
1. **`NGConstraintSpace` (Top-Down Immutable Input):**
   - `AvailableSize` (inline & block available sizes; indefinite block size `-1` for auto-height).
   - `PercentageResolutionSize` (separate from `AvailableSize` so intrinsic-width passes resolve `%` padding/margins consistently without leaking container width during `ComputeMinMaxSizes`).
   - `IsFixedInlineSize` / `IsFixedBlockSize` (forces box size instead of shrink-to-fit / auto-height, critical for grid/flex stretched items).
   - `IsShrinkToFit` / sizing constraint (`MinContent`, `MaxContent`, `FitContent`).
   - `ExclusionSpace` (immutable float/clearance geometric bands passed downward and returned in `NGLayoutResult`).
   - `BfcOffset` & `MarginStrut` (explicit margin-collapse carrier without hidden global cursor state).
2. **`MinMaxSizes` (Bottom-Up Intrinsic Pass):**
   - `ComputeMinMaxSizes(MinMaxSizesInput) -> { min_size, max_size }` computes intrinsic bounds in a single side-effect-free bottom-up pass.
   - CSS 2.1 shrink-to-fit width for `inline-block`, floats, auto tables, and flex `min-width: auto` / `flex-basis: auto` items resolves cleanly from `min(max(min_size, available), max_size)` using `MinMaxSizes`.
3. **`NGLayoutResult` + `NGPhysicalBoxFragment` (Immutable Output):**
   - Returns fragment geometry `(size, children_offsets)`, `IntrinsicBlockSize`, `ExclusionSpace` updates, `MarginStrut` (escaped top/bottom margins), baseline metrics, and inline line boxes without mutating global scratch tables across recursive calls.

---

## 2. LayoutNG Primitive Algorithms vs CSS Specifications

### 2.1 Block & Formatting Contexts (CSS 2.1/2.2 §8.3.1, §9.4.1, §9.5, §10.6.7)
- **BFC Roots (`flow-root`, `inline-block`, `flex`, `grid`, `table-cell`, `overflow != visible`, floats, abspos):**
  - Establish an isolated `ExclusionSpace`, contain all descendant floats (`auto` height >= max enclosed float bottom), and prevent margin collapsing across the BFC boundary.
  - Non-overlapping BFC boxes beside floats query `ExclusionSpace` over `[y, y + candidate_h)` and step `y` below the lowest intersecting float edge until horizontal room suffices.
- **Margin Collapsing (`MarginStrut`):**
  - Positive margins collapse via `max`, negative via `min`, mixed via `max_pos + min_neg`.
  - Empty self-collapsing blocks fold top/bottom margins into the strut; first/last children collapse through parents lacking border/padding/BFC barriers.

### 2.2 Inline Formatting Context & Line Breaking (CSS Inline / Text 3)
- **Item Collection -> LineBreaker -> Fragment Creation:**
  - `NGInlineNode` collects flat inline items (`Text`, `OpenTag`, `CloseTag`, `AtomicInline` for `inline-block`/replaced/button/form controls, `Floating`, `Control`).
  - `NGLineBreaker` consumes items into `available_width`, tracking fractional `LayoutUnit` (1/64 px) pen advance across runs, collapsed edge whitespace, and non-splittable inline-block / `nowrap` / padded atomic spans.
  - **Wrapping Rule:** When the current line already contains an item (`pen > line_start`) and an atomic item (`inline-block`, replaced, or unbreakable padded inline span) exceeds `remaining_width`, the line closes, aligns horizontally (`text-align`) and vertically (`baseline` / `sub` / `super` / `top` / `middle` / `bottom` / half-leading), and restarts at `line_start` on the next line.
  - **Shrink-to-Fit `inline-block`:** Measured via `ComputeMinMaxSizes` (`max_content` including block children, horizontal padding/border, and horizontal margins), clamped to `clamp(min_size, available, max_size)`.

### 2.3 Flexbox (CSS Flexbox 1 §9.2–§9.7)
- **Two-Phase Line Resolution:**
  1. **Hypothetical Base Size (§9.2):** Resolve definite `flex-basis` (`px`/`%`), definite main `width`/`height`, or `flex-basis: auto` via child `ComputeMinMaxSizes` (`max_content`). Clamp by `[min-width, max-width]` (with `min-width` winning over `max-width`), observing `min-width: auto` = `min(min_content, specified_size)` when `overflow == visible`.
  2. **Flex Line Partitioning (`flex-wrap: wrap` vs `nowrap`):** Accumulate hypothetical outer sizes + `column-gap` along the line; break before an item when `line_items > 0` and adding it exceeds `available_main`.
  3. **Resolve Flexible Lengths (§9.7 Freeze Loop):**
     - Compute `free_space = available_main - sum(base_sizes) - sum(gaps)`.
     - If `free_space > 0` and `sum(flex_grow) > 0`: grow proportional to `flex_grow`, freeze any item violating `max_width` (or `min_width` when zero-basis share is below minimum), and re-distribute remaining space until convergence.
     - If `free_space < 0` and `sum(flex_shrink * base_size) > 0`: shrink proportional to **scaled shrink factor** `flex_shrink * base_size` (including auto-width items!), freeze any item hitting its `min_width` / `min-width: auto` floor, and re-distribute remaining deficit among unfrozen shrinkable items until convergence.
  4. **Main-Axis Justification & Auto Margins:** After `ResolveFlexibleLengths`, remaining positive free space goes first to `margin-left/right: auto`, or else to `justify-content` (`flex-start`, `center`, `flex-end`, `space-between`, `space-around`, `space-evenly`). Items with fixed/shrunk bases NEVER overlap prior siblings because the pen strictly advances by `used_outer_size + gap + resolved_margins`.

### 2.4 CSS Grid (CSS Grid 1 §7–§12)
- **Track Initialization & Intrinsic Sizing:**
  - If `grid-template-columns` is omitted (`none`), implicit column count defaults to `1` (`grid-auto-columns` defaulting to `auto` -> stretches to container under `justify-content: normal`), still respecting Grid non-collapsing item margins and `gap`.
  - Expand `repeat(count, ...)` and `minmax(min, max)` tracks; resolve `auto-fit` / `auto-fill` when container `available_w` is finite.
  - Size `auto` / `minmax(min, max)` tracks via CSS Grid §12.5 (`base_size = max(min_content)`, `growth_limit = max(max_content)`), maximize `auto` tracks before distributing remaining space to `fr` tracks (§12.7.1, freezing tracks whose `min` floor exceeds proportional `fr` share).
  - Apply `justify-content` only when no unconstrained `fr` track exists and auto tracks didn't absorb free space.

### 2.5 CSS Table (CSS 2.1 §17.5.2.2)
- Collect rows through `<thead>`, `<tbody>`, `<tfoot>`, tracking row-group vertical bounds (`y_start .. y_end`).
- Automatic layout computes per-column `min_content` and `max_content` across cells (handling `colspan` and `min-width`/`max-width` constraints without bailing out to block flow!).
- `width: auto` tables shrink-to-fit `[sum(min), sum(max)]` against `available_w`; explicit/100% tables distribute surplus space proportionally to column flexibility.

### 2.6 Viewport Clipping & Scroll Offset
- Layout computes full document geometry `[0 .. content_height)` independent of the viewport height.
- Scrolling translates by `-scroll_y` (or applies a viewport transform), while `overflow: hidden | auto | scroll` ancestor clips remain anchored in document/owner coordinates. Viewport culling happens only at rasterization / visible tile selection — never by discarding below-the-fold retained Draw IR commands before scroll composition.
