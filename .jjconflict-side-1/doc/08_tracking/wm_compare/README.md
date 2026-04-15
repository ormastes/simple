# WM Compare Tracking

Tracking hub for `wm_compare` phase reports, runtime notes, and current truth.

## Current Runtime Truth

- Source B is the live host Web WM capture path.
- The live Web WM now serves `examples/ui/simpleos_web_wm.ui.sdn` and the
  `SimpleOS Web WM` shell, not the older Hello Electron fixture.
- The host/browser runtime is currently the most trustworthy visual source for
  the obsidian-themed WM.
- B-vs-D comparisons are still structurally limited unless both sides render
  the same scene through comparable pipelines.

## Phase Reports

| File | Purpose |
|------|---------|
| [phase1_report.md](phase1_report.md) | First live source-B capture flow |
| [phase2_report.md](phase2_report.md) | HTML compatibility investigation |
| [phase3_report.md](phase3_report.md) | Stitch/theme drift follow-up |
| [phase4_report.md](phase4_report.md) | QEMU / engine2d capture lane |
| [phase5_report.md](phase5_report.md) | Explicit bit-compare and B-vs-D blocker analysis |
| [interpreter_mirror_report.md](interpreter_mirror_report.md) | Interpreter-side compatibility notes |

## Reading Order

For current behavior, start with:

1. [phase5_report.md](phase5_report.md)
2. [doc/07_guide/tooling/wm_compare.md](../../07_guide/tooling/wm_compare.md)
3. [doc/07_guide/platform/simpleos_web_wm.md](../../07_guide/platform/simpleos_web_wm.md)

Older reports remain useful historical context, but several of them describe the
pre-obsidian or pre-live-source-B state.
