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

## Results of the first execution pass (2026-07-25, same day)

Matrix still **1/7 PASS**. But every cluster-C blocker is now identified, and two
are fixed. Four defects were found that were previously invisible:

| # | finding | status |
|---|---|---|
| P1 | **native codegen drops the receiver for non-`me` (`fn`) instance methods.** Call sites emit one register; the first arg lands in the `self` slot. `HashMap.contains_key` reads word 0 of a `text` (`"STR1"`=0x53545231), low bits match the heap tag, untag+deref → SIGSEGV. Gated on `fn_.is_mutable`, `50.mir/_MirLowering/function_lowering.spl:194`. Minimal repro: 82-byte file, one dotted `use`, `--entry-closure`. | FILED `native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25` |
| P4 | **`examples/**` isolation buffers child output and prints only after `wait()`** — a timeout kill discards everything, so slow examples show zero output AND exit 0. This is why 3 host-WM cells were misattributed as "window-only blocked". | FILED `examples_isolation_buffers_output_lost_on_timeout_2026-07-25` |
| P3 | **`MouseEvent` duplicate-type erasure** blocked the SimpleOS kernel build. | **FIXED** (`a163f3977a2`) |
| P2b | **bare-reassignment multi-line grammar gap** (`val x =\n e` parses, `x =\n e` does not). | FILED + example fixed |

### P3 SimpleOS-WM: kernel build blocker CLEARED
Before: `1 file(s) failed to compile`. After the `MouseEvent` fix:
**662 compiled, 0 cached, 0 failed**, linked 9,281 KB ELF, 25.8s compile +
81.5s link. Cell moved `wm-simple-web-build-failed` → `wm-simple-web-build-invalid-elf`.
**Next blocker (current work):** `elf_file_status`
(`check-simpleos-wm-fullscreen-evidence.shs:190-208`) requires magic `7f454c46`,
class=2 (ELF64), data=1 (LE), machine=62 (EM_X86_64). Harness targets x86_64
throughout (entry/linker-script/`--target` all `arch/x86_64`). The stale on-disk
`simpleos_wm_production_desktop.elf` (Jul 22) is **ELF32/EM_386** — leftover from
an older configuration, not today's product. Today's candidate is `rm -f`'d on
failure, so it must be rebuilt to inspect its header.

### Corrections forced by evidence (all mine)
1. **The 2D showcase never triggered the segfault.** An 82-byte file with one
   `use` does; a file with zero `use` builds fine. Closure size and the GC-tier
   import are irrelevant. My "GC-tier import causes the crash" framing was wrong.
2. **The host-WM cells were never window-blocked.** They ran; their output was
   discarded. `SIMPLE_EXAMPLE_ISOLATED_CHILD=1` → 169,612 lines vs 2.
3. **`bin/simple` is itself a Rust seed right now** (it prints the seed warning).
   Per `.claude/rules/bootstrap.md` that is an emergency stopgap, never the
   resting state — worth its own follow-up.
4. The 2D compiled lane via `bin/simple` **timed out at 20 min with zero cache
   objects** — so "use bin/simple for the compiled lane" is not yet a working
   route either.

### Deliberately NOT done
The one-word stopgap `fn contains_key` → `me contains_key`
(`hashmap.spl:99`, `hashset.spl:112`) would clear P1's crash immediately. Not
applied: it masks a general ABI defect leaving every other `fn` instance method
miscompiled. The correct fix flips the calling convention for all of them
atomically and needs its own bootstrap-verified change.

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

## Measurement discipline — updated 2026-08-05

The rule above is right but incomplete for this matrix. Three additions, all
verified against the emitters:

- **`grep 'Results:'` only matches `bin/simple test`**
  (`src/app/test_runner_new/test_runner_single.spl:225`). `bin/simple run` — the
  command this matrix uses for the showcase examples — emits a **different**
  grammar, `N examples, M failures`, singular `1 failure`, and **ANSI-wrapped**
  (`src/compiler_rust/driver/src/cli/test_output.rs:164`, `:251`). A `Results:`
  grep against `run` output finds nothing and reads as "no tests". Strip ANSI
  before anchoring; `^[0-9]+ examples` matches nothing on real output.
- **Prefer the per-file line landed in `5b57a79f8ba`:**
  `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N`
  (`src/compiler_rust/driver/src/cli/basic.rs:144`). One authoritative line per
  file, on stdout, last — it exists precisely because the per-`describe` line
  and the stderr failure line together let a red file end its stdout green.
- **Compare `executed`, not just `failed`.** A module-load failure drops whole
  `describe` blocks at exit 0, which in this matrix looks identical to a cell
  that legitimately has fewer examples. The exit-0-with-no-evidence pathology
  already recorded for Cluster B is the same failure mode seen from outside.

Full trap list, including the coverage-run flags, the waiter anti-patterns, and
the census/sabotage rules: `.claude/skills/spipe.md` §"Reading the verdict — how
a spec run lies to you".

## WM showcase lane (added 2026-08-05, docs only)

A separate lane is building a **WM showcase** — the 2D, web, and GUI-widget
windows managed together with a **taskbar derived from live window state**,
capture-verified. It is not one of the 7 cells above; it is the composition of
the Host-WM column into a single surface.

Its live-derivation path exists today
(`build_taskbar_model`, `src/app/ui.web/taskbar_shell.spl:55`, running list
built from `UiWindowSurfaceRegistry.bindings`), and the capture contract exists
(`src/os/compositor/hosted_wm_capture_evidence.spl`). What does **not** exist:
a unified driver module, and any catalog readiness — all nine
`showcase_catalog()` readiness bits are `false` and
`test/01_unit/lib/common/ui/showcase_catalog_spec.spl:55` asserts they are.

**Interaction with this replan:** the Cluster B diagnosis (`examples/**`
isolation buffers child output; a timeout kill discards it and exits 0, filed as
`examples_isolation_buffers_output_lost_on_timeout_2026-07-25`) applies directly
to any WM-showcase run launched through `examples/`. Set
`SIMPLE_EXAMPLE_ISOLATED_CHILD=1` before concluding a WM-showcase run produced
no output — that flag turned 2 lines into 169,612 during this replan.

Contract and evidence levels: `doc/03_plan/agent_tasks/showcase_apps.md`
§"WM showcase lane", `doc/05_design/showcase_apps.md`, and
`doc/05_design/showcase_apps_gui.md`.
