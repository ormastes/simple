# Feature Expert: SimpleOS WM QEMU Evidence Harness

## What this is
The QEMU-hosted test harness for SimpleOS window manager (WM) desktop, encompassing
image/disk construction, bootloader wiring, evidence-lane verification, and live
pixel capture for deterministic rendering validation.

## Source of truth
- **Harness admission:** Linked-worktree mode with version-probe seed detection
  (`fix 62e79e2d`) — gates stale binaries before QEMU spin-up
- **Evidence lanes:** Separate validation paths for different rendering backends
  (metal/vulkan/software), each with independent pixel-capture gates
- **Blocked on:** Parser ~100cps collapse on native-build lane
  (`doc/08_tracking/bug/native_build_parser_100cps_regression_2026-07-26.md`)

## Code map
| File | Role |
|---|---|
| `scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs` | Widget showcase, Vulkan backend |
| `scripts/check/check-macos-vulkan-2d-live-evidence.shs` | 2D rendering, Vulkan backend |
| `scripts/check/check-macos-metal-2d-live-evidence.shs` | 2D rendering, Metal backend |
| `scripts/check/check-macos-vulkan-web-live-evidence.shs` | Web/HTML lane, Vulkan backend |
| `scripts/check/check-portable-compute-toolchains.shs` | Cross-platform compute stack |
| `src/os/hosted/hosted_wm_evidence.spl` | Evidence collection harness (pixel comparison, metrics) |

Specs: Test-lane fixture verification (evidence gates in script suite above).

## Timeout environment knobs (2026-07-26)
- **Wall timeout must exceed worker timeout:** if harness wall-clock limit is shorter
  than worker process timeout, evidence capture silently fails
- **Per-lane configuration:** each evidence script accepts custom timeouts;
  diagnostic harness validates kernel boot completion before evidence lane spin-up

## Seed detection (admission gate)
The harness version-probes the `simple_seed` binary at startup:
- **Stale seed:** harness rejects and fails fast (do not spin QEMU against pre-stage4 binaries)
- **Missing seed:** linked-worktree mode detects via canonical release path
  (`bin/release/<triple>/simple_seed`)

## Live rendering evidence paths (2026-07-26)
- **Pass criteria:** nonzero byte count in output PPM (NOT file size)
- **Failure modes:**
  - Parser collapse → closure discovery stalls → no native code emitted → black pixels
  - Nil-self miscompile (LLVM lane) → guest crashes → empty framebuffer
  - Silent cache misses → stale binaries reused → outdated rendering logic
- **Workaround for stale cache:** forced rebuild via `--fresh-cache --full-bootstrap`
  (ensures re-run on fresh stage4 seed)

## Related layer experts
- [os_compositor](../../layer_expert/os_compositor/skill.md) — WM frame composition + scene projection
- [bootstrap](../../layer_expert/bootstrap/skill.md) — seed/stage2/stage3 redeploy gate

## Update Rule
After harness admission logic, timeout behavior, evidence-lane additions, or seed
detection changes, refresh this skill with new configuration knobs and validation
paths.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
