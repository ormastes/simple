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

### (a) "Three host-WM cells unblocked, real window rendered at `54ed5df7c8b`" — CLAIMED (real prior evidence, no artifact here)

- `54ed5df7c8b` is, by its subject line,
  `fix(seed-interp): register rt_string_to_int + rt_raw_i64_to_string in
  EXTERN_DISPATCH` (2026-07-28) — PROVED by `git log -1`. Campaign memory
  records that fix's *effect* as unblocking the host-WM cells, with
  captured evidence (`WIN 2097154`, `windows=1 taskbar_items=1`, 550s
  under Xvfb). Those are two linked facts, not a mislabeled commit: the
  hash is the EXTERN_DISPATCH fix AND the window render is real prior
  evidence. **The status point stands regardless: no artifact verifies it
  on THIS host at THIS tip, so the correct status is CLAIMED** — the
  earlier evidence is not discarded, it is simply not re-verified here.
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

## Host-WM gate run (2026-07-30) — cells stay BLOCKED, now on a PROVISIONING gap

`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` (51KB,
modified 2026-07-30 02:12) was run to settle cells #4-#6. **It cannot
reach a pass on this host.** The gate is a provenance-attesting gate:
every rejection below is an anti-fabrication guard, which is exactly why
it cannot be cheaply faked — and why the prior macOS evidence came from a
machine that had the assets.

Gate contract (PROVED by reading): entry `src/os/hosted/hosted_entry.spl`
native-built with `SIMPLE_LIB=src`; writes
`build/linux-hosted-wm-live-window-evidence/` (`report.md`, `hosted-wm`,
`build.log`, window PNG, framebuffer PPM, snapshot); ~25 sub-assertions
(`framebuffer`, `live_window`, `glyph_crop`, `focus`, `pointer`,
`keyboard`, `text`, `input_receipt`, `semantic`, `replay_rejection`,
`move`, `maximize`, `restore`, deliberate-red calibration, ...) reduced
to `linux_hosted_wm_live_window_status=pass|fail`. Budgets:
`LINUX_HOSTED_WM_LIVE_TIMEOUT_SECS` default 60 (window wait),
`LINUX_HOSTED_WM_BUILD_TIMEOUT_SECS` default 600 (native-build) — so a
genuine full run is ~10 min, consistent with the 550s prior evidence.

Wall chain, each PROVED by execution (every attempt ≤1s, so no timeout or
kill-daemon interaction was possible; 4 daemon PIDs were live throughout):

| # | `reason=` | Meaning | Satisfiable here? |
|---|---|---|---|
| 1 | `source-provenance-unavailable` | requires clean `src/os`+`src/lib`; the shared working copy had **29** uncommitted changes | YES — re-run in a clean worktree; `source_provenance_status=pass` confirmed |
| 2 | `explicit-simple-bin-required` | `SIMPLE_BIN` must be passed explicitly | YES |
| 3 | `rust-seed-forbidden` | rejects the Rust seed (correct per the pure-Simple standing rule) | YES — `build/redeploy_out/simple_stage2` (pure-Simple lineage) accepted |
| 4 | `runtime-provider-explicit-required` | `SIMPLE_WM_RUNTIME_LIB` must be passed explicitly | YES |
| 5 | `runtime-provider-sha` | caller must attest the provider's sha256 (`SIMPLE_WM_RUNTIME_LIB_SHA256`; no hardcoded pin) | YES — attesting the true sha is intended usage, not a bypass |
| 6 | `runtime-provider-bootstrap-forbidden` | the **bootstrap** runtime `.so` is explicitly rejected | **NO** — the only self-hosted-lineage runtime lib on this host is the bootstrap one |
| 7 | `pinned-font-asset-invalid` (unreached, but unreachable-to-pass) | hardcoded pin `FONT_ASSET_SHA256=2cb2adb3…` on `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf` | **NO** — `assets/fonts/` holds **0 tracked files at tip** and the directory is absent from the working tree; the asset is not in the repo at all |

**Verdict: cells #4-#6 remain BLOCKED — but the blocker is now precisely
characterized and it is NOT a WM defect, NOT the co-import defect (proved
gone above), and NOT Xvfb.** It is an **asset/runtime-provider
provisioning gap**: two independent, deliberately-pinned prerequisites
(a non-bootstrap self-hosted runtime provider `.so`; the pinned font
asset) are simply not present on this host. Status vocabulary updated
from UNKNOWN to BLOCKED for #4-#6 on that basis.

Not fixed here, per brief: provisioning a pinned font asset and producing
a non-bootstrap self-hosted runtime provider are neither one-liners nor
this pass's scope, and the gate must not be weakened to accommodate their
absence. Settling requirements for #4-#6 are therefore:
1. provision `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
   matching sha256 `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`
   (decide whether it belongs in-repo or in a fetch step — its absence
   makes this gate unrunnable on any fresh checkout, which is a
   reproducibility hole in the campaign's most load-bearing gate);
2. produce a non-bootstrap self-hosted runtime provider `.so` and pass it
   with its attested sha;
3. then run the gate in a clean worktree (walls 1-5 are already known
   satisfiable) and capture `window_id` + PNG/PPM + the ~25 statuses.

**Revised scoreboard: 0 GREEN, 2 CLAIMED, 5 BLOCKED, 0 UNKNOWN** — no
cell moved to GREEN, but three moved from UNKNOWN to BLOCKED-with-a-named
cause and an actionable provisioning list, and the campaign now knows its
top gate cannot run on a fresh Linux checkout as shipped.
