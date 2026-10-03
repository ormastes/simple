# rendering_buffer_preexisting_spec_failures_2026-10-03

Status: items 4–5 fixed (workaround) 2026-10-03; see Landing below
Date: 2026-10-03
Lane: rendering buffer hardening (skia side)
Runtime note: all runs below are seed-run (diagnostic — not release-admissible),
Rust seed binary `bin/simple`, `--mode=interpreter`, in a shared dirty worktree
with parallel lanes actively editing the same files.

This release copy documents ONLY the two items owned and fixed by the
rendering-buffer perf/mem lane (items 4–5). The shared-worktree copy on main
additionally tracks unrelated lanes' items 1–3.

## Item 4 (fixed)

`test/01_unit/lib/skia/raster_prims_spec.spl`
- "stroke_path of a line segment produces non-empty pixels"
  (`semantic: undefined field: unknown property, key, or method 'r' on
  Dict`).
  Root cause: seed test-runner type-erasure defect, NOT a raster_prims bug —
  reproduced with the W1 `Bitmap.zeros` hunk reverted; identical code passes
  under `bin/simple run` and with inline (unbound) arguments.
  Fix: the spec passes the color inline instead of via a `val` binding; the
  behavior under test is unchanged. Spec now 13/13.
  Root cause tracked in
  doc/08_tracking/bug/seed_val_bound_class_type_erasure_spec_context_2026-10-03.md.

## Item 5 (fixed)

`test/01_unit/lib/skia/engine2d_bridge_spec.spl`
- "rejects rounded corners whose coverage ignores disabled antialiasing"
  (`'blend_mode' on Dict`): same seed type-erasure defect as item 4. In the
  shared worktree the spec passes the paint inline; the case itself is
  uncommitted parallel-lane content and is intentionally NOT part of this
  release commit.

## Landing

- Branch: work/rendering-buffer-perfmem-20261003 (target release/1.0).
- Commit: the tip of work/rendering-buffer-perfmem-20261003
  ("fix(engine2d,skia): rendering buffer perf/mem hardening + regression
  specs"; `git log -1 --format=%H origin/work/rendering-buffer-perfmem-20261003`).
