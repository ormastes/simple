# `test/05_perf/ui_slim/ref/` — reference-only C UI fixtures

Work package A08 of `doc/03_plan/ui/slim_kernel_plugin/plan.md`. These are
**comparison references, not production backends and not a promotion proposal**
(a provider promotion is an A00 decision).

| Entry | Purpose |
|---|---|
| `FILE.md` | this manifest |
| `run_t1_lib.shs` | shared real-pty T1 harness + sabotage selftest |
| `termbox2/` | `t1_termbox2.c`, `build.shs`, `run_t1.shs` |
| `ncursesw/` | `t1_ncursesw.c`, `build.shs`, `run_t1.shs` |
| `vendor/` | vendored upstream source — external path, excluded from owned-code counts |
| `nuklear/`, `microui/`, `fltk/` | GUI references — work package **A09**, not owned by A08 |

Guide: `doc/07_guide/ui/ui_slim_c_references.md`.
Build artifacts and receipts land in `build/ui_slim/ref/` (untracked).
