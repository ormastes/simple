# Slim-UI GUI reference fixtures (A09)

**Date:** 2026-09-06 · **Work package:** A09 (`doc/03_plan/ui/slim_kernel_plugin/plan.md`, Wave 1)
**Design:** `doc/01_research/ui/slim_kernel_plugin/simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md` §4, §8.1, §8.2
**Fixtures:** `test/05_perf/ui_slim/ref/{microui,nuklear,fltk}/` · **Vendored upstream:** `test/05_perf/ui_slim/ref/vendor/`
**Sibling guide (different owner):** `doc/07_guide/ui/ui_slim_c_references.md` (termbox2, ncursesw — A08)

These fixtures are **reference-only diagnostics**. They exist so the slim-UI lane
has a measured, reproducible sense of what external C/C++ UI stacks cost in
isolation. **No number here is a comparison against Simple**, and none of it is
part of the Simple product.

## The two categories are not comparable to each other

Design §4 [W07] is explicit: a complete-window result is a *different category*
from a headless widget-core result. This guide keeps them in separate tables and
you must not merge the rows.

### (a) `widget-core-headless`

The widget core runs on a fixed input script. There is **no window, no renderer,
no rasterizer, no compositor, no font baking**. The library builds its retained
state and emits a draw-command list; the fixture counts that list and stops.

| library | pinned commit | frames | draw cmds / run | wall ms (median of 10) | min / max | stripped bytes | build warnings |
|---|---|---|---|---|---|---|---|
| microui | `0850aba860959c3e75fb3e97120ca92957f9d057` | 100 | 1500 | 0.0495 | 0.0470 / 0.0670 | 51,864 | 0 |
| Nuklear | `e3e18dc1e4d3de935095d372aaa211f12183befb` | 100 | 1000 | 0.0810 | 0.0560 / 0.1540 | 226,168 | 2 (upstream `nk_inv_sqrt`, `nk_file_load` unused-function; recorded, not suppressed) |

Both fixtures build the same scene — a panel titled `Simple UI Reference`, the
greeting `Hello from Simple UI!`, and a `Click me` button — and feed the same
script: pointer drift over frames 0-9, hold on the button centre, press on
frame 50, release on frame 51.

### (b) `visible-window`

A real native window on a real display server, with the greeting and a button,
input-ready, closed deterministically.

| library | status | reason |
|---|---|---|
| FLTK | **unsupported** | Not installed on this host (`fltk-config` absent, no `fltk` brew formula, no `FL/` headers under `/opt/homebrew`, `/usr/local`, `/usr`) and A09 forbids installing anything. `test/05_perf/ui_slim/ref/fltk/run.shs` re-probes all four locations on every invocation and exits **2** `ERROR — nothing was checked (...)` naming each probe. |

There is deliberately **no `main.cpp`** in the FLTK directory. An unbuilt, unrun
C++ file is dead code, and any headless stand-in would be a substitute for
exactly the thing this category exists to measure. The row stays `unsupported`
until FLTK is actually present; it never becomes a number.

**When FLTK does arrive**, the header comment in `fltk/run.shs` specifies the
contract: `Fl_Window` + `Fl_Box` greeting + `Fl_Button`, `--auto-quit-ms 500`
closing the window from `Fl::add_timeout` after the first draw, and a first-draw
time measured from process start. That time is labelled **in-process
first-draw** and is *not* an external presentation timestamp — design §8.3 is
explicit that a successful submit or a returned `draw()` is not a display
timestamp. Producing `launch_to_observed_presentation` needs an external
observer this lane does not have; that cell stays `NOT_MEASURED`.

## What the numbers mean, and what they do not

**Draw-command count** is the number of commands the library appended to its own
command list for one frame of the scripted scene. It is:

- a measure of how much work the widget core hands to a renderer, and a stable
  fingerprint of the scene (both fixtures verified byte-deterministic across all
  10 runs — `draw_commands_deterministic: 1` in the receipts);
- **not** pixels, triangles, or GPU work — nothing is rasterized;
- **not** comparable between microui and Nuklear as "efficiency": the two split
  a frame into commands with different granularity (Nuklear emits its own
  rect/border/text primitives, microui emits clip/rect/text), so 1500 vs 1000 is
  a difference in *decomposition*, not in cost;
- **not** comparable to any Simple draw/DrawIR count, which is a different IR.

**Wall time** is `CLOCK_MONOTONIC` around the 100-frame loop only. It excludes
process start, library init and teardown. It is 50-80 microseconds for 100 frames
in both cases — well inside run-to-run spread on this shared box (microui
0.0470-0.0670, Nuklear 0.0560-0.1540) and below the noise floor of anything else in this plan —
treat the two as `INCONCLUSIVE` against each other, per the plan's rule that
differences within noise are never wins.

**Stripped size** is a whole-fixture binary, statically containing the library
plus the fixture's own `main`. It is not the library's own footprint and not
resident memory. Design §8.4: loaded-library file size is not RSS.

**Nothing here measures Simple.** Design §8.2 warns specifically against
comparing a C native executable to a Simple compiler/interpreter process; on
this host the Simple side is additionally blocked (plan Blocker 1: `bin/simple`
is a bootstrap shim, so every Simple UI number is seed-lane diagnostic).

## Build lines

Recorded per run in `build/ui_slim/ref/<name>.receipt.sdn` (compiler version,
flags, link line, warning count, upstream pin, unstripped/stripped bytes, run
count, medians, and the asserted greeting).

```
Apple clang version 17.0.0 (clang-1700.6.4.2)   # not upstream LLVM/clang
cc -O2 -Wall -I<ref>/vendor/microui -o microui_ref main.c vendor/microui/microui.c -lm
cc -O2 -Wall -I<ref>/vendor/nuklear -o nuklear_ref main.c -lm     # single-header
```

## Running them

```sh
sh test/05_perf/ui_slim/ref/microui/run.shs --runs 10
sh test/05_perf/ui_slim/ref/nuklear/run.shs --runs 10
sh test/05_perf/ui_slim/ref/fltk/run.shs          # exits 2, unsupported
sh test/05_perf/ui_slim/ref/<name>/run.shs --selftest
```

Verdict is always the last line of stdout: `PASS — ...` (0), `FAIL — ...` (1),
`ERROR — nothing was checked (...)` (2). The selftest runs unconditionally
before every timing run and is fatal.

### What each run asserts

1. `frames=100` — the loop actually ran.
2. `greeting_frames=100` — the greeting is in the **draw-command stream** on
   every frame, compared against a canonical `EXPECTED_GREETING` that the
   sabotage switch cannot redefine. (A first attempt let sabotage redefine both
   the rendered and the asserted string; the build then agreed with itself and
   the selftest passed vacuously. That is why the two constants are separate.)
3. `submit_count >= 1` — the scripted click actually hit the button. A click
   that lands on empty panel still emits a full frame of draw commands and would
   satisfy (1) and (2) while proving nothing about input.
4. Draw-command count identical across all runs.

**Sabotage selftest:** a `-DSABOTAGE_NO_GREETING` build replaces the rendered
greeting. It must fail assertion (2). If it does not, the runner reports
`FAIL — selftest sabotage was not detected; the greeting assertion is vacuous`
and refuses to produce a number. The sabotage build goes to a separate path and
never overwrites the measured binary or its receipt.

## Pointer targeting (why there are no hardcoded coordinates)

- **Nuklear:** `nk_widget_bounds()` reports the next widget's screen rect without
  consuming the layout slot, so the click target is read out of Nuklear itself.
- **microui:** the button is placed at an explicit absolute rect via
  `mu_layout_set_next()`, so the target *is* the widget rect. Reading it back
  from the command list is not viable — microui reorders root-container commands
  with jump commands, so list order is not emission order. (Attempting that
  first yielded a 1-pixel-wide scrollbar rect and a silently missed click:
  `submit_count=0` with a full 1500-command frame.)
- **microui** only registers hover on a frame where the button is not already
  held (`mu_update_control`'s `!mouse_down` gate), so its press frame must be
  preceded by pure motion. Nuklear's mechanism is different — `nk_button_label`
  fires on *release* inside the rect that received the press — so both scripts
  use the same motion/press/release shape for different reasons.

## macOS limits on this host

- **Apple clang 17.0.0**, not upstream LLVM/clang. The repo's pinned LLVM 23
  toolchain (`scripts/setup/llvm-toolchain-env.shs`) is a Linux-host deployment;
  these numbers are Apple-clang numbers. `CC` is honoured by both runners.
- **No FLTK, and installing is out of scope** — see the `visible-window` table.
- **No `/proc`, no `smaps`/PSS, no xvfb.** Design §8.4's Linux memory lane has no
  equivalent here; per the plan's translation table those rows are `unsupported`,
  not silently substituted with RSS.
- **Shared, busy box.** Wall times are diagnostic single-digit-microsecond
  measurements taken without a runner lock. Design §8.5 requires 20 warmups +
  100 interleaved launches under an exclusive lock for anything certified; 10
  runs is a pilot, and it is labelled `diagnostic` in every receipt.
- **Font metrics are synthetic** (8 px/char advance, 16 px line) in both
  fixtures. That is deliberate — it keeps glyph rasterization out of the number
  and the frame deterministic — but it means these are not text-shaping numbers.

## Vendoring

`test/05_perf/ui_slim/ref/vendor/<lib>/README.md` carries the upstream URL, the
pinned commit, the exact list of files taken, and the license copied verbatim.
Per CLAUDE.md Owned-Code Scope those directories are **not owned code**: exclude
them from counts, reviews and verification scans.

Only the library translation units were vendored (microui: `src/microui.{c,h}`;
Nuklear: `nuklear.h`). Upstream demo/example/font trees were deliberately not
copied — they are unused and adding hundreds of files would press against the
tree-size push guard's band (`scripts/check/check-tree-size-push.shs`). Each
clone's `.git` was deleted after recording `rev-parse HEAD`.

| library | license |
|---|---|
| microui | MIT (© 2024 rxi) |
| Nuklear | MIT **or** Unlicense, licensee's choice (© 2017 Micha Mettke) |
