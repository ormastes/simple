# Showcase matrix — fresh evidence on current main (2026-07-25)

Binary: deployed stage4 self-hosted `bin/simple` → `bin/release/aarch64-apple-darwin-macho/simple`
(built from main `4ed680f5`, redeploy gate 11/11; verified intact this session — the seed WARNING
it prints in some run lanes is the known cosmetic misdetection, see
`doc/08_tracking/bug/seed_binary_detection_gaps_2026-07-25.md`). Main range during evidence
collection: `a5e5afb8`…`b5a009cc`.

## Matrix

| Cell | Lane | Verdict | Evidence |
|------|------|---------|----------|
| widget × headless | interpreted | **PASS** | 640x480 P6 PPM, 74 distinct byte values, 921,600/921,600 nonzero px, 24 widget types, sha256-verified font raster (cold=10, warm-hits=20); repeat PASS 320x240 from true `examples/` path post-watchdog-fix (64 distinct bytes, 95s CPU) |
| 2D × headless | interpreted | **PASS** (rerun 2026-07-26 after `f99057d8` font digest fast path) | 320x240 software offscreen: exit 0 in 103s under heavy CPU load; `graphics_2d_nonzero=76789/76800` (matches 07-18 baseline), `checksum=1108808631`, `semantic_differences=4`, font identity matched with cold=11/warm-hit=22 cache pattern. Prior FAIL (40+ min, perf boundary) superseded |
| web × headless | interpreted | **FAIL (honest gate)** | `status=fail reason=blank-or-uniform pixels=172800 nonzero=172800 checksum=1322071898` — deterministic across scratchpad + true examples path. Root-caused: 10s paint budget expires under interpreter (only canvas-background paints); crash precursor fixed (`c6469f6c74`); RCA: `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md`. Cell remains compiled-lane-gated |
| widget × host-WM | window | **BLOCKED** | **CORRECTED 2026-07-27 — see note below; earlier attribution was WRONG.** Real blocker: **compile dies in the SEMANTIC phase** — co-importing `common.ui.wm_app_process_contract` (:32) and `std.nogc_sync_mut.ui.gui_renderer` (:17) yields `error: semantic: Cannot resolve module: common.ui.wm_app_process_contract`. `GuiRenderer.create` is never reached, no window is attempted; under Xvfb: `APP_EXITED_EARLY after 17s`, `window_id=NONE`. Filed: `doc/08_tracking/bug/co_import_makes_module_unresolvable_wm_contract_gui_renderer_2026-07-27.md` |
| 2D × host-WM | window | **BLOCKED** | same semantic-phase co-import defect (`gui_renderer` :9, contract :25); ancillary offscreen synthetic WM-chrome capture PASS (`check-hosted-wm-capture-evidence.shs`: 16x16 crop, 90/256 non-background px, checksum 473142143, theme aetheric_dark) |
| web × host-WM | window | **BLOCKED** | same semantic-phase co-import defect (`gui_renderer` :9, contract :24) |
| SimpleOS-WM × QEMU | native-build+boot | **UNVERIFIED** | An unretained local x86 rerun53 reportedly passed after font-catalog memoization (`cf09420b88`), but no report, captures, hashes, or build/runtime attestation were committed, so it is not acceptance evidence. The latest canonical tracked report (`simpleos_wm_fullscreen_evidence_2026-07-24.md`) remains **FAIL** with `reason=wm-simple-web-build-failed`; ARM and the required x86/ARM SIMD receipts remain unverified. The font pipeline anomaly also remains open: the reported local run had `has_ttf=0` on 117/118 metric resolves (`pointer_release_font_metrics_hang_2026-07-26.md`). |

### Correction 2026-07-27 — the host-WM blocker attribution above was wrong (retracted, not silently rewritten)

The three host-WM rows originally read: *"wrappers are window-only (`SIMPLE_GUI=1` +
`GuiRenderer.create`); concurrent live window-evidence loops own the single-window capture lane."*
**That is DISPROVEN.** Kept visible here so nobody re-derives it:

- **Xvfb is NOT the blocker.** `/usr/bin/Xvfb` and `/usr/bin/xvfb-run` are present, and
  `scripts/check/check-linux-hosted-wm-live-window-evidence.shs:419,502` already spawns Xvfb with
  `WINIT_UNIX_BACKEND=x11`. Display availability and capture-lane contention are solved.
- The wrappers **never get far enough to touch a display**. They die in the semantic phase, before
  codegen — so no display-lane or capture-lane fix can change this outcome.
- The headless-lane gap (`doc/08_tracking/bug/wm_showcase_no_headless_lane_2026-07-25.md`) is a real
  gap but is **not** what blocks these three cells.
- Real blocker, reproduced deterministically (~14s) on two independent binaries and prefix-independent:
  `doc/08_tracking/bug/co_import_makes_module_unresolvable_wm_contract_gui_renderer_2026-07-27.md`.
  Root cause under investigation, fix in flight.

## Defects fixed during collection (all pushed)
- `--timeout` not propagated to `SIMPLE_TIMEOUT_SECONDS` (`a5a4f8250`)
- font_registry `[u8] as [i64]` interpreter cast crash (`c6469f6c74`)
- examples watchdog pipe deadlock >64KB (`a5e5afb8`) — validated live: examples-path widget went watchdog-kill → PASS
- delegate_run idempotency hardening (`cf0b5cd6`)

## Defects filed during collection (all pushed)
- watchdog pipe deadlock RCA + parser `self.`-hint spam (`b509b8a1`)
- web paint-budget interpreter gap (`44278e48`)
- host-WM headless-lane gap + seed-binary detection gaps (`b5a009cc`)
- `cli` mnemonic-token native-build parser regression — fix in progress (agent), will need stage4 rebuild+redeploy for the harness to re-run

## Observations
- In-process `--timeout` also failed to fire on the scratchpad lane (2D ran 40+ min past `--timeout=1200`) — same defect class as the propagation fix; recorded here.
- The matrix's honest-fail machinery worked: web `blank-or-uniform` and the seed-reject provenance gates caught exactly what they were designed to catch; no cell was stamped over fake evidence.
