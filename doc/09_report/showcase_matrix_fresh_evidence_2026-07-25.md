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
| 2D × headless | interpreted | **FAIL (perf boundary)** | 320x240 software offscreen: no evidence line after 40+ min (killed); log 75k lines dominated by diagnostic spam. Regression-flagged vs 07-14 "2D 320x240 standalone PASS" note |
| web × headless | interpreted | **FAIL (honest gate)** | `status=fail reason=blank-or-uniform pixels=172800 nonzero=172800 checksum=1322071898` — deterministic across scratchpad + true examples path. Root-caused: 10s paint budget expires under interpreter (only canvas-background paints); crash precursor fixed (`c6469f6c74`); RCA: `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md`. Cell remains compiled-lane-gated |
| widget × host-WM | window | **BLOCKED** | wrappers are window-only (`SIMPLE_GUI=1` + `GuiRenderer.create`); concurrent live window-evidence loops own the single-window capture lane. Gap filed: `doc/08_tracking/bug/wm_showcase_no_headless_lane_2026-07-25.md` |
| 2D × host-WM | window | **BLOCKED** | same; ancillary offscreen synthetic WM-chrome capture PASS (`check-hosted-wm-capture-evidence.shs`: 16x16 crop, 90/256 non-background px, checksum 473142143, theme aetheric_dark) |
| web × host-WM | window | **BLOCKED** | same |
| SimpleOS-WM × QEMU | native-build+boot | **FAIL (new regression found)** | harness `check-simpleos-wm-fullscreen-evidence.shs`: provenance/font/qemu/grub/OVMF stages PASS; kernel native-build FAILS — `cpu.spl:105 fn cli():` → `expected Ident, got cli 'cli'` (lexer has a `cli` token in the native-build lane only; plain `run` parses it fine on both binaries). QEMU never launched. Last PASS 07-18/19 → regression window since |

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
