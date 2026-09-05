# WM lane rung (d) blocked: `.wm-window` gradient layer fails the cpu-composited-material admission contract

- **ID:** wm_window_bg_layers_reject_cpu_composited_material_2026-08-08
- **Status:** SUPERSEDED — root cause below is WRONG. See
  `doc/08_tracking/bug/wm_guest_css_var_unresolved_blocks_material_admission_2026-08-09.md`

> **Correction (2026-08-09).** The claim that `mat_layers == ""` is the
> *single* failing term is refuted by measurement. `backdrop_len=21` is
> `blur() saturate(170%)`, which `simple_web_backdrop_admission` **rejects**
> (the blur term must end in `px)`) — scored "pass" below from its length
> alone, never evaluated. `bg=352321535` (`0x14FFFFFF`) is the gradient's
> first stop, not the theme surface (`rgba(31,31,33,0.80)`). All three
> numbers — `bg=352321535`, `layers_len=73`, `backdrop_len=21` — reproduce
> exactly and only when the sheet's `var(--…)` references do not resolve.
> `layers_len=73` is the gradient plus a **bare trailing comma**, not the
> two-layer background (which measures 93 when `--app-surface` resolves).
> Both fixes proposed below ("composite the layer", "drop the gradient from
> the theme") would have left the backdrop term failing and would not have
> unblocked the lane; the theme is not at fault.
- **Severity:** high (sole blocker for SimpleOS x86_64 WM lane rung (d) — an
  in-guest rendered WM frame accepted as evidence)
- **Found by:** SimpleOS x86_64 WM fullscreen evidence lane, 2026-08-08
- **Lane:** `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`

## Summary

Every WM window is rejected by the Simple Web material provenance contract
because the `aetheric_dark` theme gives `.wm-window` a **two-layer**
background. The single failing predicate term is `mat_layers == ""`.

This is a genuine content/contract mismatch, **not** a timeout, **not** a
resolution/capacity problem, and **not** an evidence-emission gap.

## Evidence

Isolated run, real firmware (OVMF pflash + GRUB multiboot, no `-kernel`, no
`isa-debug-exit`), `SIMPLEOS_WM_READINESS_TIMEOUT_MS=420000`,
`BUILD_DIR=build/wm_lane_iso_opus`. Serial log 27,487 bytes.

Guest serial (verbatim):

```
[web-style-producer] entry-rejected index=4 mode=engine2d-cpu-composited-material-v1 bg=352321535 gf=0 gt=0 layers_len=73 backdrop_len=21 animation=none
[wm-frame] content-provenance-rejected window_id=1 status=engine2d_rendered backend=software fallback=none material= theme=aetheric_dark source=e13114ec...
[wm-frame] window-degraded window_id=1 reason=unresolved-or-duplicate-content
[wm-frame] content-provenance-rejected window_id=2 ... (identical)
[wm-frame] content-provenance-rejected window_id=3 ... (identical)
```

Gate verdict: `status=fail reason=guest-render-fault` (tripped by
`serial_has_production_fault` matching `content-provenance-rejected`).

## Root cause

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`
admission predicate:

```
val cpu_admitted = (
    material_channel_ready and static_material and
    wm_material_mode == "engine2d-cpu-composited-material-v1" and
    wm_fallback == "solid-material" and declared_opaque and
    translucent_surface and mat_layers == "" and
    typed_stops_valid and backdrop.admitted)
```

Term-by-term against the observed values:

| term | observed | verdict |
|------|----------|---------|
| `wm_material_mode` | `engine2d-cpu-composited-material-v1` | pass |
| `translucent_surface` | `bg=352321535` = `0x14FFFFFF`, alpha 20 | pass (0 < 20 < 255) |
| `typed_stops_valid` | `gf=0 gt=0` (both absent) | pass |
| `backdrop.admitted` | `backdrop_len=21` | pass |
| `static_material` | `animation=none` | pass |
| **`mat_layers == ""`** | **`layers_len=73`** | **FAIL** |

`mat_layers` is `st.bg_layers_raw`. Its 73-char value is the gradient layer
from `src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl`:

```css
.widget-panel, .wm-window {
  background: linear-gradient(180deg, rgba(255,255,255,0.08), rgba(255,255,255,0.025)), var(--app-surface);
}
```

(`linear-gradient(180deg, rgba(255,255,255,0.08), rgba(255,255,255,0.025))`
is 72 chars + separator.)

`solid_admitted` cannot rescue it either — that branch requires
`wm_material_mode == ""`, and the mode here is non-empty.

With `cpu_admitted` and `solid_admitted` both false, no material entry is
emitted, so the frame carries `material_fallback_kind=none` and an empty
`material_fallback_sha256`. `wm_content_frame_web_provenance_valid`
(`src/lib/common/ui/window_scene.spl:354`) then fails on
`_wm_lower_hex_sha256_valid(frame.material_fallback_sha256)`, and all three
windows are degraded.

## Fix direction (design call — do NOT simply relax the predicate)

Relaxing `mat_layers == ""` would weaken a provenance contract and must not be
done to make the gate green. Two honest options:

1. **Extend the contract**: admit a single translucent-white
   `linear-gradient` overlay layer, composite it in the CPU material path, and
   include the layer in the material digest so provenance still describes what
   was actually drawn.
2. **Change the theme**: drop the gradient layer from `.wm-window` so the
   surface is a single `var(--app-surface)` colour, matching what the CPU
   material path can honestly attest.

Option 1 preserves the intended Aetheric look; option 2 is the smaller change.
Either way the material digest must describe the real composited result.

## Secondary finding — the 60s readiness default masks this defect

`READINESS_TIMEOUT_MS` defaults to `60000`. At 4K under QEMU **TCG** the boot
does not reach the first frame in 60s, so the lane reported the misleading
`dynamic-scanout-or-desktop-readiness-missing` (serial log 15,638 bytes,
truncated mid-first-frame at `[wm-frame] host-gpu-fallback`). Raising the
window to 420s reached the real failure above (27,487 bytes) and the accurate
`guest-render-fault`.

Recommended: raise the lane default (waits for the **same** markers — no gate
semantics change), and/or enable KVM. `/dev/kvm` is present and usable on this
host and the user is in the `kvm` group, but the lane's QEMU launch passes no
`accel`, so it runs TCG (~30x slower, per the in-source note at
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`).

Not filed as a bypass: neither change alters any required marker.

## Notes on things that were ruled OUT

- **Host-GPU fallback is by design.** `[wm-frame] host-gpu-fallback
  reason=unavailable-or-readback-capacity` occurs because the lane's QEMU
  launch has **no ivshmem device**, so
  `map_qemu_host_gpu_ivshmem_bar2_active_vmm()` returns 0 and `base == 0`.
  Software compositing is the intended path here.
- **Not a readiness-emission gap.** `[production-readiness]` is emitted at
  `gui_entry_desktop.spl:611`, *after* `render_baremetal_first_frame` returns
  a positive revision at line 572 — the ordering is already honest.
- **Not a 4K capacity refusal.** The frame reached
  `status=engine2d_rendered backend=software`, so 3840x2160 software
  compositing completed; the rejection is downstream of rendering.

## Related

- `doc/08_tracking/bug/simple_web_readiness_marker_aspirational_diskless_2026-07-20.md`
  (superseded in part: the disk mount now works — three process-owned
  surfaces materialize, `owned=3`, so the lane is no longer diskless)
- `doc/08_tracking/bug/simpleos_wm_4k_footprint_exceeds_heap_window_2026-07-14.md`
