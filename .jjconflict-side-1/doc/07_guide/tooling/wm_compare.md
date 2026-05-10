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
  --source-a=test/baselines/wm_compare/four_windows/B_live.ppm \
  --source-b=test/baselines/wm_compare/engine2d_in_qemu/D.ppm \
  --out-dir=test/baselines/wm_compare/phase5
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

---

## Artifacts

Artifacts are written under:

```text
test/baselines/wm_compare/<scene>/
```

Typical files:

- baseline PPMs such as `A.ppm`, `B_live.ppm`, `D.ppm`
- diff outputs such as `diff_A_vs_B.ppm`
- `report.sdn`

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
