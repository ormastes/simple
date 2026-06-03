# Graphical Backend Equality — Next Plan

Date: 2026-06-03

## Current Status

Implementation started. The common `wm_compare` equality model and render-side
capture facade exist, with focused system/integration specs and mirrored
manuals.

## Recommended Path

Use Feature Option B with NFR Option 2 if the goal is to refactor tests around a
common interface and make backend drawings equivalent across rendering and
WM/web comparison. Use Option A if the next slice must be smaller.

## Proposed Contract

- `RenderCase`: canonical drawing scene shared by all tests.
- `GraphicalBackendSpec`: URI-like selector for `2d:*`, `web:*`, `gui:*`, and
  `wm:*` lanes.
- `GraphicalCapture`: RGBA pixels plus logical size, physical size,
  scale factor, content rect, panel rect, outer window rect, capture kind, and
  color space.
- `GraphicalEqualityReport`: backend status, capture status, metadata status,
  shape/pixel/color status, tolerance policy, and artifact paths.

## Implementation Phases After Selection

1. Add the common test-facing model in `src/app/wm_compare/`. Done.
2. Add SPipe specs proving backend selector parsing, capture metadata
   validation, and failure classification. Done.
3. Add or repair an Engine2D capture wrapper so real `RenderBackend`/`Engine2D`
   readback can feed equality reports instead of fixture-only buffers. Done.
4. Convert one existing `wm_compare` fixture and one existing Engine2D parity
   fixture to use the same `RenderCase`. First focused Engine2D filled-rect
   capture fixture is done.
5. Add exact CPU/software equality and GPU/web diagnostic policy.
6. Generate or update the mirrored `doc/06_spec/...` manual.
7. Run focused verification and `find doc/06_spec -name '*_spec.spl' | wc -l`.

## Verification Start Set

- `sh scripts/install-spipe-dev-command.shs --check`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check <changed src/spec files>`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/system/wm_compare/<new spec>.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple run test/integration/rendering/engine2d_cpu_metal_parity_run.spl`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

## GitHub Sync

Run `jj git fetch` at each checkpoint. Rebase only after unrelated dirty files
are understood or cleared by their owner. Push only after verify passes and the
user approves.
