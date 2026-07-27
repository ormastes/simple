# WM windows can realize NO material on the software/freestanding backend — every content frame is provenance-rejected

- **Filed:** 2026-07-26
- **Status:** open, root-caused, not fixed
- **Regressed by:** `6b18dcd874f fix(wm): preserve Aetheric Web glass material`
- **Blast radius:** SimpleOS-WM x QEMU showcase cell went PASS -> `guest-render-fault`.
  Every window in the composition is dropped, so the lane never reaches capture
  and produces no PPMs.

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

An A/B against a pre-regression tree is what caught this. A single-tree repro of
a symptom that the pre-regression tree also produces attributes nothing.
