# Historical report: WM windows realized no material on one software/freestanding guest run

- **Filed:** 2026-07-26
- **Status:** source contract reconciled; current-runtime verification open
- **Historical attribution (superseded by the reconciliation below):**
  `6b18dcd874f fix(wm): preserve Aetheric Web glass material`
- **Blast radius:** SimpleOS-WM x QEMU showcase cell went PASS -> `guest-render-fault`.
  Every window in the composition is dropped, so the lane never reaches capture
  and produces no PPMs.

## 2026-07-27 source reconciliation

The retained guest A/B output below remains useful diagnostic history, but its
original CSS-admission diagnosis no longer describes current source.
`6b18dcd874f` added two pieces the diagnosis omits:

- custom properties are resolved before declaration parsing; and
- exactly one linear highlight plus one base color is normalized to typed
  gradient/base fields with an empty raw-layer rejection witness.

The committed production Aetheric spec exercises that exact package CSS and
requires resolved `blur(30px) saturate(170%)`, the typed two-stop gradient, and
one material witness. A later one-file change removed the producer mode while
leaving those requirements intact, making the source and its tests
contradictory. The producer mode is restored, and the production spec now
continues through Engine2D software execution and requires the matching CPU
receipt.

No current, source-matched pure-Simple GUI runtime is available on this host;
the active GUI launcher delegates to `simple_seed`. Therefore neither the old
guest failure nor the repaired source is promoted to a current runtime result.
The sections below describe the historical observation and hypothesis; the
remaining bug is obtaining revision-bound native/guest execution evidence.

## Symptom

`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (rerun56):

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=guest-render-fault
baseline/fullscreen/restored ppm_file_status=missing   (all three)
```

`build/simpleos_wm_fullscreen_evidence/serial.log`, once per window:

```
[wm-frame] content-provenance-rejected window_id=1 status=engine2d_rendered
    backend=software fallback=none material= theme=aetheric_dark source=e13114ec...
[wm-frame] window-degraded window_id=1 reason=unresolved-or-duplicate-content
```

`fallback=none material=` (empty) is `WebRenderMaterialFallbackProvenance.none()`
verbatim — the frame carries no realized material at all, so
`wm_content_frame_web_provenance_valid` (`src/lib/common/ui/window_scene.spl:338`)
rejects it and the executor degrades every window.

## Root cause: the two admission paths are mutually exclusive for WM windows

`_simple_web_material_witness`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:145`)
admits exactly two realizations per node:

- `cpu_admitted` requires `mode_attr == "engine2d-cpu-composited-material-v1"`
  **and** a translucent surface **and** `backdrop.admitted` — a byte-exact
  `blur(Npx) saturate(M%)` resolved onto the node.
- `solid_admitted` requires `mode_attr == ""` ("exact mode must be absent; all
  material fields must already be gone").

The WM content producer
(`src/os/compositor/simple_web_window_renderer.spl:76`) now stamps
`data-wm-theme-material-mode='engine2d-cpu-composited-material-v1'` on **every**
window unconditionally.

On the freestanding/software backend backdrop sampling is not available (the
desktop entry says so itself:
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl:289` prints
`backdrop_filter=unavailable fallback=solid-material`). So:

- `cpu_admitted` is false — no admissible backdrop.
- `solid_admitted` is false — the exact mode attribute is present.

Witness counts stay 0 -> `simple_web_layout_material_provenance_after_execution`
returns `.none()` -> provenance gate rejects -> all windows degraded.

The same mode attribute also switches off the legacy solid reduction in the
style producer (`simple_web_html_layout_renderer_core.spl:1859`, guarded by
`wm_material_mode != "engine2d-cpu-composited-material-v1"`), which is the path
that used to hand these frames a real solid-material digest. That is why the
cell was green before this commit and red after it.

The producer's own comment states the intended behaviour — "when backdrop
sampling is not available it preserves the resolved surface as an opaque solid
material" — but with the exact mode declared there is no code path that can
reach that outcome.

## Two candidate resolutions (owner's call)

1. **Producer declares only what the backend can realize.** Emit
   `data-wm-theme-material-mode` only where backdrop sampling exists; without it
   the legacy solid reduction runs and yields a genuine solid-material digest.
   Keeps the witness's exactness intact.
2. **Witness admits a documented reduction:** solid when the exact mode is
   declared but the backdrop is inadmissible *and* the realized surface is
   already opaque and flat. This contradicts the comment on `solid_admitted`
   ("solid reduction is not a lossy fallback for a failed CPU contract"), so it
   is only right if that rule was meant to constrain producers rather than
   backends.

Not fixed here: the regressing commit is another session's in-flight feature and
its files were mid-rebase with unresolved conflict markers in the shared working
copy at the time of filing (`simple_web_html_layout_renderer.spl`,
`simple_web_layout_engine2d_fast.spl`, `engine.spl`,
`src/app/simpleos_gpu_host/main.spl`). Patching a contract under an active
rebase would have raced it.

## Verification trap: the host repro does NOT attribute this

`probes/dg_wm_material_provenance.spl` reproduces `material_kind=none valid=false`
on the host — but it does so **identically at `6b18dcd874f^`**, where the lane
was green. Both host runs break for a different reason:

```
[web-style-producer] budget-break at=0 of=7 now_us=... deadline_us=...   (deadline ~6s in the past)
```

The host seed bails out of JIT (`HIR lowering error: Unknown variable:
composite_over_base while lowering fb_background_radial_stack_clip`) and
interprets everything, so the 10s render budget is already spent before the
style loop starts; no node gets a style, so the witness is empty regardless of
which tree is under test. The guest serial log has **zero** budget-break lines,
so the guest failure is the mode-attribute contradiction above, not starvation.

Raising the budget does not rescue the probe: with
`SIMPLE_WEB_RENDER_BUDGET_MS=900000` both trees still break, together, at
`at=2 of=7` (the stage re-arm in `_web_budget_rearm` partitions the total across
style/layout/paint, so a bigger total only buys the style stage a longer slice —
the interpreter still overruns it). Pre- and post-glass outputs stayed identical
field for field in both configurations.

An A/B against a pre-regression tree is what caught this. A single-tree repro of
a symptom that the pre-regression tree also produces attributes nothing.

## What DOES attribute it

Guest lane, same harness, two trees:

- rerun56 — current main: `status=fail reason=guest-render-fault`, no PPMs,
  3x `content-provenance-rejected`.
- rerun57 — `6b18dcd874f^` plus this session's five level-gated files:
  `status=pass reason=pass`, all three PPMs (24,883,217 B each),
  `restored_sha256 == baseline_sha256` (`68adc6e8...`),
  `changed_bytes=23054033`, font region `addf76ed...`, corrupt-copy rejection
  pass, zero production faults, zero gated probe lines.

The delta between those two runs is the regressing commit, and rerun57 also
clears the level-gating landed alongside it (the WM file set is layout-sensitive,
so that had to be shown, not argued).
