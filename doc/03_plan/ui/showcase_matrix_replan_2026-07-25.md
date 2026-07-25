# Showcase matrix — deep replan after research (2026-07-25)

Supersedes the sequencing in `doc/03_plan/ui/engine2d_gc_tier/plan_2026-07-25.md`.
That plan's Phase 1 recommendation is **withdrawn** — see "Corrections" below.

Status at replan: **1/7 cells PASS** (`widget × headless`).

## What the research changed

Four parallel investigations (3 returned at time of writing) plus two direct
experiments. The matrix's 7 cells are not 7 problems. They are **three root-cause
clusters**, and the cheapest path through them is not the one the previous plan
chose.

### Cluster A — the interpreter is structurally too slow for the GC-tier renderers
Cells: `2D × headless`, `web × headless`.

- **web**: budget is `WEB_RENDER_BUDGET_MS = 10000`
  (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:70`).
  Raising it does not help: with a **600,000 ms (10 min)** budget the renderer was
  **still inside layout after 15 minutes at 480×360**. This is orders of
  magnitude, not a tuning miss. The RCA explicitly rejects raising the budget and
  names a compiled lane as the fix. Report line 15 already says
  *"Cell remains compiled-lane-gated."*
- **2D**: 40-min stall, root-caused to an **interpreter** GC root-scan blowup
  (`doc/01_research/ui/engine2d_gc_tier/analysis_2026-07-25.md`).
- Both renderers sit on `gc_async_mut` (web:
  `std.gc_async_mut.gpu.browser_engine.simple_web_renderer`; 2D:
  `std.gpu.engine2d.engine`). The tier disease is **systemic, not Engine2D-specific.**

**Key consequence:** compiling these showcases bypasses the interpreter entirely.
Both failures are *interpreter* failures. A compiled lane fixes both cells
**without** porting anything off the GC tier.

### Cluster B — host-WM wrappers emit nothing
Cells: `widget × host-WM`, `2D × host-WM`, `web × host-WM`.

A headless lane was added to all three wrappers (pinned by
`test/03_system/check/wm_host_headless_capture_spec.spl`). But running
`SIMPLE_WM_HEADLESS_CAPTURE=1 <fullcli> run examples/06_io/ui/wm_widget_showcase_gui.spl`
produced **2 lines of output, both the runtime seed warning** — no status key, no
PPM, exit 0. An exit-0 with no evidence is worse than a failure: it reads as
success to anything checking only the return code. Diagnosis in flight.

### Cluster C — native-build/parse defects that block Cluster A's fix
This cluster is the *reason* Cluster A is not already solved.

| defect | evidence | status |
|---|---|---|
| `native-build` **SIGSEGV** on the 2D showcase | `REAL_EXIT=139`, core dumped, **zero diagnostic output**, `--entry-closure`, reproduced at both 30 GB and 60 GB caps (so not a `ulimit` artifact) | NEW — file it |
| `web_render_file_gui.spl` parse error | `Unexpected token: expected expression, found Indent` — identical on the new full CLI **and** the older deployed binary, so pre-existing, not a regression | open |
| SimpleOS kernel `fn cli():` | **FIXED** — `d5a6312da1b` un-reserves `cli`; verified in the *native-build lane specifically*, compiled+linked+ran `cli()=42` | resolved |

## Corrections to the previous plan

1. **Withdrawn: "port the 2D showcase to the nogc scene-graph API."** The nogc
   `Engine2D` (`src/lib/nogc_sync_mut/engine/core/engine.spl`) defines **5 methods
   total** (`to_text`, `create`, `create_with_config`, `get_node`,
   `get_renderer_mode`) and **0 of the ~50** methods the showcase calls — it
   exposes no draw and no text API at all. The old plan said to prefer this
   "if the scene graph already covers the showcase's primitives." It covers none.
2. **The tier fix is no longer the critical path.** It is real and still worth
   doing, but it is not what unblocks these cells.

## Revised priority (highest leverage first)

**P1 — Fix the `native-build` SIGSEGV on the 2D showcase.**
This single defect gates the compiled lane, which gates **2 cells**. It crashes
with no diagnostics, so step one is getting a backtrace (core dump / gdb), not a
guess. Owner: hard — needs compiler-internals judgment.

**P2 — Run the compiled lane for `2D × headless` and `web × headless`.**
Blocked on P1 for 2D; `web` additionally needs the `Indent` parse bug fixed (its
child process is `web_render_file_gui.spl`). Exit: a real PASS or an honest-fail
line that is *not* budget-expiry.

**P3 — `SimpleOS-WM × QEMU`.** Prerequisites all present (QEMU 8.2.2, OVMF,
compiler with the fix). Harness `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
**Already launched.** Cheapest available cell.

**P4 — Host-WM silent exit (3 cells).** One diagnosis likely unblocks all three,
since the wrappers share the lane. Pending research.

**P5 — Tier cleanup / de-duplication.** Unchanged from the prior plan, including
`P3.3 make same-name collisions loud at registration` — still the best
recurrence-prevention item. Explicitly **not** on the critical path.

## Sub-module assignment (model tiering)

Per `feedback_research_on_cheap_models`: sonnet for scoped investigation, opus for
synthesis and compiler-internals judgment.

| # | Sub-module | Model | Why |
|---|---|---|---|
| P1 | native-build SIGSEGV backtrace + root cause | **opus** | compiler internals, no diagnostics to start from |
| P2a | compiled-lane run for 2D once P1 lands | sonnet | mechanical once unblocked |
| P2b | `Indent` parse bug in `web_render_file_gui.spl` | sonnet | localized parse defect, clear repro |
| P3 | SimpleOS-WM harness + evidence capture | sonnet | scripted harness, verdict-reading |
| P4 | host-WM silent-exit diagnosis | sonnet | single-file control-flow trace |
| P5 | tier de-dup + loud collisions | opus | cross-cutting, correctness-sensitive |
| — | matrix synthesis / report | opus | integrates all lanes |

## Honest risk notes

- The compiled lane **bypasses** the GC-tier problem for these cells; it does not
  fix it. Any code legitimately holding a GC-tier object while mutating a large
  array stays exposed. Do not report P2 success as "the tier bug is fixed."
- If P1's segfault turns out to be in the same parse-retention neighborhood as
  `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`, **stop and check
  that doc first** — it is 976 lines, actively owned by another session, and was
  re-derived from scratch once already today at a cost of two 100 GB runs.
- Measurement discipline: verdicts come from `grep 'Results:'` / artifact
  existence, never from a `tail`, and never from a pipeline's exit code (`| tail`
  masked a SIGSEGV as `EXIT=0` during this very replan).
