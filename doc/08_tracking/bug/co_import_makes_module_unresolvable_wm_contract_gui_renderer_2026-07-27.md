# Co-importing `wm_app_process_contract` + `gui_renderer` makes the contract module unresolvable

- **ID:** co_import_makes_module_unresolvable_wm_contract_gui_renderer_2026-07-27
- **Date:** 2026-07-27
- **Area:** semantic phase — module resolution / import registration
  (post-`module_registry.spl` deletion, `src/compiler/20.hir` refactor — see *Leads*)
- **Severity:** high — blocks **three of the five remaining showcase-matrix cells**.
  Compilation dies in the SEMANTIC phase; no codegen, no process, no window.
- **Status:** OPEN. **Root cause under investigation, fix in flight.** The
  reproduction below is proven and minimal; the mechanism is NOT yet proven.

## Symptom

Two imports that each resolve **fine on their own** become fatal when placed in
the same file:

```
use common.ui.wm_app_process_contract.{wm_fs_bridge_decode}
use std.nogc_sync_mut.ui.gui_renderer.{GuiRenderer}
```

```
error: semantic: Cannot resolve module: common.ui.wm_app_process_contract
```

The module that fails is the **first** one — the one that resolves perfectly
when the `gui_renderer` import is deleted. Nothing about the contract module
itself changed; only the presence of a *second, unrelated* import did.

## Reproduction (minimal, ~14s, deterministic)

Kept inline here deliberately — the originals live in a scratchpad that gets
swept.

`combo.spl` — fails:

```
use common.ui.wm_app_process_contract.{wm_fs_bridge_decode}
use std.nogc_sync_mut.ui.gui_renderer.{GuiRenderer}

fn main() -> i64:
    val d = wm_fs_bridge_decode("")
    print "ok"
    0
```

`combo2.spl` — fails **identically**, proving the defect is prefix-independent:

```
use std.common.ui.wm_app_process_contract.{wm_fs_bridge_decode}
use std.nogc_sync_mut.ui.gui_renderer.{GuiRenderer}

fn main() -> i64:
    val d = wm_fs_bridge_decode("")
    print "ok-std-prefix"
    0
```

Controls: delete **either** `use` line and the remaining one resolves and the
file compiles. Only the **combination** fails.

## What is proven

- **Combination-only.** Either import alone resolves. This is not a broken
  module and not a broken import path.
- **Prefix-independent.** `common.ui.…` and `std.common.ui.…` fail identically,
  so this is not a `std.`-prefix rewriting/aliasing bug.
- **Deterministic**, ~14 seconds, every run. No flake, no ordering dependence
  across runs.
- **Not binary-specific.** Reproduced on **two independent binaries**:
  the deployed `bin/simple` and `simple.pre-riscv-fix-bak`. So it is not a stale
  or half-deployed artifact.

## Second symptom — same defect, lower severity (believed)

In the full showcase wrappers the failure sometimes surfaces **one step later**,
as:

```
error: semantic: unknown extern function: rt_string_to_int
```

- declared: `src/lib/common/ui/wm_app_process_contract.spl:4`
  (`extern fn rt_string_to_int(value: text) -> i64`)
- called: `src/lib/common/ui/wm_app_process_contract.spl:178`
  (`val parsed = rt_string_to_int(raw)`)

Both sites are in the **same file** that supposedly failed to resolve. That is
the informative part: the module sometimes registers **PARTIALLY** — its
function bodies are reachable enough to be type-checked, but its `extern`
declarations are not. So the bug is better described as *import registration
being clobbered/truncated by a co-import* than as a flat "module not found".

## Blast radius

All three host-WM showcase wrappers import both modules and therefore all three
die in the semantic phase:

| file | `gui_renderer` | `wm_app_process_contract` |
|---|---|---|
| `examples/06_io/ui/wm_widget_showcase_gui.spl` | :17 | :32 |
| `examples/06_io/ui/wm_graphics_2d_showcase_gui.spl` | :9 | :25 |
| `examples/06_io/ui/wm_web_standards_showcase_gui.spl` | :9 | :24 |

Consequence: **`GuiRenderer.create` is never reached and no window is ever
attempted.** Under Xvfb the widget cell reports `APP_EXITED_EARLY after 17s`,
`window_id=NONE` — which reads like a windowing failure and is not one.

This blocks three of the five remaining showcase-matrix cells (widget, 2D, web
— all × host-WM).

## What does NOT attribute this — Xvfb is NOT the blocker

This matters because **the project's own report said otherwise**
(`doc/09_report/showcase_matrix_fresh_evidence_2026-07-25.md`, host-WM rows,
now corrected).

- `/usr/bin/Xvfb` and `/usr/bin/xvfb-run` are **present**.
- `scripts/check/check-linux-hosted-wm-live-window-evidence.shs:419,502`
  **already spawns Xvfb** with `WINIT_UNIX_BACKEND=x11`.
- Display availability and capture-lane contention are therefore **solved**.

The prior claim that these wrappers are "window-only (`SIMPLE_GUI=1` +
`GuiRenderer.create`)" and blocked by "concurrent live window-evidence loops
owning the single-window capture lane" is **not what blocks them**. The process
never gets far enough to open a display connection. Any fix aimed at the
display lane will change nothing here.

## Leads (NOT conclusions)

- **Related suspect class only: flat-registry name collision.** Same family as
  the known `interp env_get` defect and
  `doc/08_tracking/bug/text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27.md`
  — a flat, name-keyed registry hijacking an explicit `use`. The *shape* fits
  (one explicit import defeated by the presence of another). **Do not assert
  this is the mechanism.** It is unproven here; a fix agent is investigating
  now.
- **Possible fresh regression.** `module_registry.spl` was recently **deleted**
  and `src/compiler/20.hir` refactored. If import registration moved during that
  refactor, a co-import clobber is a plausible outcome. **This is a lead, not a
  conclusion** — no bisect has been run.

## Workaround

None clean. Do **not** split the wrappers into two modules to dodge the
co-import; that hides a compiler defect in product code and would have to be
reverted. If a temporary unblock is needed for evidence capture, note it
explicitly as a workaround against this ID so it is removed when the fix lands.

## Proper fix

Root-cause the semantic-phase import registration so that registering a second
module cannot un-register or partially-register a first. The **partial**
registration (extern decls lost while function bodies survive — see *Second
symptom*) is the sharpest lead into the mechanism: whatever path drops the
extern table is likely the same path that drops the whole module in the harder
case.

### Regression test

A two-import fixture exactly like `combo.spl` above, asserting it compiles.
Cover both prefixes (`common.ui.…` and `std.common.ui.…`) and assert the
`rt_string_to_int` extern resolves. Also add the three showcase wrappers to a
semantic-phase compile gate so a semantic-phase death can never again be
reported as a windowing/Xvfb problem.

**Do NOT weaken a gate or skip a test to make this green.** Project rule.

## Related

- `doc/09_report/showcase_matrix_fresh_evidence_2026-07-25.md` — host-WM rows;
  previously mis-attributed to Xvfb/capture-lane, corrected to point here.
- `doc/08_tracking/bug/wm_showcase_no_headless_lane_2026-07-25.md` — the
  separately-filed headless-lane gap. Real, but **not** what blocks these three
  cells.
- `doc/08_tracking/bug/text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27.md`
  — flat-registry name-collision class, **suspect only**.
- `.claude/memory` `feedback_interp_struct_name_collision_global_registry` —
  same-name-in-two-modules collisions, struct counterpart.
