# Window-scene Draw IR coverage run stalls before closure

The combined coverage run for `window_scene_draw_ir.spl` made no progress for
more than four minutes and required termination (exit 143). Its partial CSV
contains runtime-hit decisions only and does not expose the complete static
denominator for the 1,765-line owner.

Required fix: split or instrument the owner so pixel storage, scene projection,
composition, and executor behavior have bounded measurable ownership; add a
native owner harness with explicit timeout/progress and static branch manifest.
Do not infer coverage from only the decisions emitted before termination.
