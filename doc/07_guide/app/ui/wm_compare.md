# WM Compare Guide

`wm_compare` is the screenshot capture and comparison harness for the Window
Manager render lanes.

It does not define the WM runtime. It captures and compares artifacts produced
by other runtimes.

---

## Source Modes

The harness currently understands three source labels:

| Source | Meaning |
|--------|---------|
| `A` | Electron reference capture |
| `B` | Live host Simple Web WM capture |
| `D` | QEMU Simple OS capture via QMP screendump |

Current source-B behavior is important:

- source B is a live capture of the running localhost Web WM page
- it is not an in-process placeholder renderer anymore
- the `scene` name controls output naming and report grouping, but does not
  change the served HTML fixture by itself

---

## Main Modes

`src/app/wm_compare/main.spl` currently supports these higher-level modes:

| Mode | Purpose |
|------|---------|
| default capture flow | capture one or more sources by label |
| `live_b` | capture and persist live source-B output |
| `bit-compare` | compare two explicit PPM inputs |
| `live_bd_compare` | capture live B and compare against D |

---

## Typical Commands

### Capture real SimpleOS QEMU and host GTK WM parity evidence

Use this wrapper when the task asks for a real GUI/WM lane instead of a fake
QMP capture. It runs from the repository root, launches the SimpleOS desktop
under QEMU when `QEMU_AUTO_LAUNCH_SIMPLEOS_DESKTOP=1`, captures the framebuffer
through QMP `screendump`, and also runs the host GTK/GL exact-scene baseline:

```bash
QEMU_AUTO_LAUNCH_SIMPLEOS_DESKTOP=1 \
  BUILD_DIR=build/qemu_gtk_wm_capture_evidence \
  REPORT_PATH=doc/09_report/qemu_gtk_wm_capture_evidence_$(date -u +%F).md \
  timeout 180 sh scripts/check/check-qemu-gtk-wm-capture-evidence.shs
```

The wrapper chains the host scene baseline through:

```bash
sh scripts/check/check-gtk-gl-wm-scene-bitmap-evidence.shs
```

Current passing evidence requires:

- `qemu live bitmap status: pass`
- `live capture full-scene mismatches: 0`
- `host GTK GL WM scene status: pass`
- `host GTK GL WM scene mismatch count: 0`
- `host GTK GL WM scene blur/tolerance used: false`

The host GTK baseline does not by itself promote guest-side performance. A
release-grade pass requires both a host GTK baseline and a QEMU guest Simple
paint marker shaped like:

```text
[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=<positive> iterations=<positive> timing_unit=tsc
```

### Capture live source B

```bash
src/compiler_rust/target/bootstrap/simple run src/app/wm_compare/main.spl -- \
  --source=B \
  --scene=four_windows \
  --mode=live_b
```

### Compare two explicit captures

```bash
src/compiler_rust/target/bootstrap/simple run src/app/wm_compare/main.spl -- \
  --mode=bit-compare \
  --source-a=test/09_baselines/wm_compare/four_windows/B_live.ppm \
  --source-b=test/09_baselines/wm_compare/engine2d_in_qemu/D.ppm \
  --out-dir=test/09_baselines/wm_compare/phase5
```

---

## Current Truth About Parity

The harness works, but not every comparison is meaningful.

Important current limitation:

- B and D are not yet a true parity pair for the same runtime scene
- B is the live obsidian-themed Web WM
- D is still tied to a different guest capture path

So a B-vs-D mismatch is often reporting a real structural difference, not a
harness bug.

Use `wm_compare` today for:

- live capture persistence
- source drift detection
- artifact generation
- bounded comparison reports

Do not over-interpret B-vs-D as proof of WM equivalence unless both sides are
known to render the same scene through comparable pipelines.

For the SimpleOS desktop/GTK lane, prefer
`scripts/check/check-qemu-gtk-wm-capture-evidence.shs` over ad hoc `wm_compare`
captures. That wrapper now owns the canonical real-QEMU QMP screendump plus
host GTK/GL exact-scene evidence and writes the release-auditable report under
`doc/09_report/`.

---

## Artifacts

Artifacts are written under:

```text
test/09_baselines/wm_compare/<scene>/
```

Typical files:

- baseline PPMs such as `A.ppm`, `B_live.ppm`, `D.ppm`
- diff outputs such as `diff_A_vs_B.ppm`
- `report.sdn`

## Publishing To SSPEC

When a WM comparison backs a TUI/GUI SSPEC, copy or emit the reviewable image
evidence under `doc/06_spec/image/<spec-relative-path>/` and list it in the
spec docblock with `**Screenshots:**` or `**TUI Captures:**`. Keep structured
reports and logs under `build/test-artifacts/<spec-relative-path>/`.

For phase-by-phase history and current blockers, see
[doc/08_tracking/wm_compare/README.md](../../08_tracking/wm_compare/README.md).

---

## Operational Advice

- Treat source B as the current host/browser truth.
- Refresh baselines when the Web WM fixture or theme intentionally changes.
- Keep phase reports honest: note when a comparison is structural rather than a
  regression signal.
- If a run depends on the live Web WM, verify the browser runtime first with
  [platform/simpleos_web_wm.md](../platform/simpleos_web_wm.md).
