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
| widget × host-WM | window | **BLOCKED** | wrappers are window-only (`SIMPLE_GUI=1` + `GuiRenderer.create`); concurrent live window-evidence loops own the single-window capture lane. Gap filed: `doc/08_tracking/bug/wm_showcase_no_headless_lane_2026-07-25.md` |
| 2D × host-WM | window | **BLOCKED** | same; ancillary offscreen synthetic WM-chrome capture PASS (`check-hosted-wm-capture-evidence.shs`: 16x16 crop, 90/256 non-background px, checksum 473142143, theme aetheric_dark) |
| web × host-WM | window | **BLOCKED** | same |
| SimpleOS-WM × QEMU | native-build+boot | **PASS** (peer rerun53, origin `bddcff5a17`; not independently reran this session) | `status=pass reason=pass`, zero production faults, `changed_bytes=23054033`, `restored_sha256 == baseline_sha256` (byte-exact restore), font region matches pinned oracle. Unblocked by font-catalog memoization (`cf09420b88` — `selected_font_asset_candidates()` was rebuilding 16 structs from string literals hundreds of times per frame, so the pointer-release render finished inside budget; it was slowness, never a hang). STILL OPEN and does not affect the green: `has_ttf=0` on 117/118 metric resolves (most WM text uses the legacy bitmap fallback, real font pipeline unhealthy — `pointer_release_font_metrics_hang_2026-07-26.md`). Perf/observability defects fixed en route this session (all pushed): parser ~100cps collapse root-caused to O(N) enum/closure registry scans and fixed (`3da818508d29`), incremental cache + live trace + kill grace (`a90c1680`), harness seed-probe/admission/timeout fixes (`62e79e2d`); those deploy when the stage4 link unblocks (`stage4_tip_link_bare_extern_symbols_2026-07-26.md`, peer capsule-producer in progress) |

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
