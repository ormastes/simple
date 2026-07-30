# Showcase matrix — evidence-based census (2026-07-30)

Purpose: re-measure the top line after many hours in blockers. **No cell
count here is taken from a report that claims success; every row states
what artifact would verify it and whether that artifact exists on THIS
host at THIS tip.**

Tip audited: `be0da59cfe3c47354ab6f47df2b3e5fd86a4e77d`.
Host: Linux x86_64, load 25-54, `kill_simple_monitor` daemon live.

## Authoritative cell definition

`doc/09_report/showcase_matrix_fresh_evidence_2026-07-25.md` (lines
11-19) — the only file in the repo that enumerates exactly 7 cells as a
matrix with per-cell verdicts and evidence. Cell names below are
**verbatim** from its table; no gate script enumerates the 7 cells, so
this report is the definition of record (PROVED by reading it).

## Finding that invalidates every prior cell count (PROVED)

That definition's evidence was collected with
`bin/release/aarch64-apple-darwin-macho/simple` — a **macOS aarch64**
binary — from main `4ed680f5`. On this host:

- that binary path **does not exist** (`bin/release/` holds only
  `linux-x86_64`, `x86_64-unknown-linux-gnu`, `riscv64-unknown-simpleos`,
  `x86_64-unknown-simpleos`);
- `4ed680f5` is **1,898 commits** behind the audited tip
  (`git rev-list --count 4ed680f5..be0da59c`).

Therefore **no cell is GREEN on this host today** — not even the two
long-standing "PASS" cells. They are CLAIMED: the artifacts are real but
were produced on another platform, 1,898 commits ago. "2/7 green" is not
a statement about this host at this tip.

## Census

| # | Cell (verbatim) | Lane | Status | Evidence / why | Settling command |
|---|---|---|---|---|---|
| 1 | `widget × headless` | interpreted | **CLAIMED** | 640x480 P6 PPM, 921,600/921,600 nonzero px, sha256-verified font raster — but macOS aarch64 binary @ `4ed680f5`, 1,898 commits stale; no artifact on this host. PROVED stale, INFERRED still-passing | re-run the widget headless render on a Linux-built `bin/simple` and re-capture the PPM + nonzero/checksum counts |
| 2 | `2D × headless` | interpreted | **CLAIMED** | `graphics_2d_nonzero=76789/76800`, `checksum=1108808631`, 103s CPU (rerun 2026-07-26) — same stale-platform caveat. PROVED stale, INFERRED still-passing | re-run the 320x240 software offscreen 2D render on this host; compare `graphics_2d_nonzero` + `checksum` to 76789/76800 and 1108808631 |
| 3 | `web × headless` | interpreted | **BLOCKED** (honest FAIL) | `status=fail reason=blank-or-uniform pixels=172800 nonzero=172800 checksum=1322071898`, deterministic. Named blocker: 10s paint budget expires under the interpreter so only the canvas background paints — `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md`. Coordinator notes module compile alone exceeded 48 min under load and the JIT path is one `text.from_any` fix from a real measurement. PROVED (blocker doc + verdict both tracked) | land the `text.from_any` fix, then run the web headless render on the COMPILED lane (the cell is explicitly compiled-lane-gated) |
| 4 | `widget × host-WM` | window | **UNKNOWN** (was BLOCKED; named blocker is STALE) | See "Host-WM" below — the documented blocker no longer reproduces. No window artifact has ever been produced for this cell on this host. PROVED that the blocker is gone; status beyond that never measured | `scripts/check/check-linux-hosted-wm-live-window-evidence.shs` (spawns Xvfb, `WINIT_UNIX_BACKEND=x11`) and capture `window_id` + a non-uniform screenshot |
| 5 | `2D × host-WM` | window | **UNKNOWN** (same) | Same stale blocker. Ancillary evidence exists but is NOT this cell: `check-hosted-wm-capture-evidence.shs` passed an *offscreen synthetic* WM-chrome capture (16x16 crop, 90/256 non-background px, checksum 473142143) — synthetic offscreen chrome is not a live window | same gate as #4, 2D wrapper |
| 6 | `web × host-WM` | window | **UNKNOWN** (same) | Same stale blocker; also inherits #3's paint-budget problem once a window opens | same gate as #4, web wrapper |
| 7 | `SimpleOS-WM × QEMU` | native-build+boot | **BLOCKED** | The definition itself records **UNVERIFIED**, explicitly rejecting an unretained local pass as non-acceptance evidence; latest canonical tracked report (`simpleos_wm_fullscreen_evidence_2026-07-24.md`) is **FAIL** `reason=wm-simple-web-build-failed`. Current named blocker: guest boots then hits a **missing-vtable `ud2` in `engine2d_draw_ir_render_batch_embedded`**. Open font anomaly: `has_ttf=0` on 117/118 metric resolves (`pointer_release_font_metrics_hang_2026-07-26.md`). PROVED (all tracked) | fix the missing-vtable `ud2`, then `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` for serial transcript + fullscreen capture |

**Scoreboard on this host at this tip: 0 GREEN, 2 CLAIMED, 2 BLOCKED, 3 UNKNOWN.**
(The two BLOCKED are #3 and #7; the three UNKNOWN are the host-WM row.)

## The two load-bearing claims, checked

### (a) "Three host-WM cells unblocked, real window rendered at `54ed5df7c8b`" — REFUTED as stated

- `54ed5df7c8b` is **not a host-WM commit**: it is
  `fix(seed-interp): register rt_string_to_int + rt_raw_i64_to_string in
  EXTERN_DISPATCH` (2026-07-28). PROVED by `git log -1`. The
  window-rendered claim is **misattributed** to this hash.
- The *real* named blocker for all three cells — a semantic-phase
  co-import failure where importing `common.ui.wm_app_process_contract`
  together with `std.nogc_sync_mut.ui.gui_renderer` gave
  `error: semantic: Cannot resolve module` — is recorded **OPEN** in
  `doc/08_tracking/bug/co_import_makes_module_unresolvable_wm_contract_gui_renderer_2026-07-27.md`
  (mtime Jul 27 23:59).
- **That blocker no longer reproduces (PROVED).** Co-importing both
  modules at this tip runs clean: `rc=0`, zero `Cannot resolve module`
  occurrences, prints `COIMPORT_OK`, cold-cache (`.simple` removed) as
  well as warm.

So the correct statement is neither "unblocked with a window rendered"
nor "blocked": the blocker is **gone**, and the cells are **UNKNOWN**
because no live-window artifact was ever produced for them here. The
next action on these three is cheap and well-defined (gate #4 above),
which is the actionable half of this census.

### (b) "widget and 2D headless are the long-standing 2/7 green" — CLAIMED, not GREEN

Both cells' artifacts are real and internally consistent, but were
produced on a macOS aarch64 binary 1,898 commits ago and cannot be
verified on this host without a re-run. Per the brief I did not force a
green: each re-run is a multi-minute render under load 25-54 (the 2D
cell already has a recorded 40+ minute FAIL at a perf boundary), so
these stay CLAIMED with the settling commands stated above.

## Incidental finding (new, not previously tracked)

The co-import probe surfaced a **Cranelift JIT bail on this path**:
`Module error: function '_sorted_timer_stats' creates a lambda/closure`,
which silently falls back to the interpreter. Relevant to the host-WM
cells because the interpreter fallback is exactly what makes #3's paint
budget expire; worth a look before measuring #4-#6 for performance
rather than mere window existence. PROVED (observed in the probe's
stderr); impact on the cells INFERRED.

## Method note

Cheap verifications only, per the brief. The one gate-scale reproduction
I ran (co-import, documented at ~14s) was chosen because it settles
three cells at once; it completed in under a second. No expensive render
or QEMU gate was run to manufacture a green, and every unverified row
carries the exact command that would settle it.
