# Layout Framework Local Research — TLDR

- Structural contract source was absent; the plan depended only on architecture pseudocode.
- Canonical CPU oracle: browser flat-array `layout()`/`LayoutResult`, not legacy BeLayoutBox.
- Text shaping stays behind the existing font owner through `TextMeasurePort`.
- Dirty/conflicted browser files are not touched by the common framework lane.

Source: `layout_framework.md`.

