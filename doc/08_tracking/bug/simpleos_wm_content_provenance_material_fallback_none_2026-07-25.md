# SimpleOS-WM cell: frame renders correctly but is rejected — `material_fallback_kind=none`, empty material digest

- **ID:** simpleos_wm_content_provenance_material_fallback_none_2026-07-25
- **Status:** OPEN — characterised and narrowed, root cause NOT established
- **Severity:** medium — blocks the `SimpleOS-WM × QEMU` showcase-matrix cell at
  the *render-provenance* stage, which is the stage after disk staging (now
  passing)

## Where the cell is now

Every earlier blocker on this cell is cleared. From the 2026-07-25 run:

```
simpleos_wm_fullscreen_kernel_build_status=current-source-built
simpleos_wm_fullscreen_disk_image_status=pass          <-- FAT32 work landed
simpleos_wm_fullscreen_serial_log_bytes=181335         <-- guest boots and runs
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=guest-render-fault
```

| # | blocker | status |
|---|---|---|
| 1 | `fn cli():` parsed as a reserved token | fixed (`d5a6312da1b`) |
| 2 | duplicate `MouseEvent` -> `struct 'ANY' field 'left_just_pressed'` | fixed (`a163f3977a2`) |
| 3 | ELF gate asserted ELF64 on the ELF32 multiboot wrap | fixed by gate owner |
| 4 | staged FAT32 image failed `fsck.fat` | fixed (`37cda4b`, fsck exits 0) |
| 5 | **this** — content provenance rejected | OPEN |

## `guest-render-fault` is a misleading label — nothing faulted

The reason string suggests a CPU fault. There is none. `serial.log` contains
exactly two `[fault]` lines and both are handler *installation*:

```
[fault] _fault_handler addr=0x00000000080002f0
[fault] _fault_handler patched -> _rich_fault_entry
```

`serial_has_production_fault()` (`check-simpleos-wm-fullscreen-evidence.shs`,
grep `serial_has_production_fault`) matches an alternation of eight patterns.
Counted individually against the log, exactly one matches — and it is not a
fault:

```
^\[wm-frame\] content-provenance-rejected      1
(all seven others)                             0
```

**Anyone triaging this from the reason string alone will look for a page fault
that does not exist.** Count the patterns individually before assuming which
arm of an alternation fired.

## The measurement

The single matching line:

```
[wm-frame] content-provenance-rejected window_id=1 status=engine2d_rendered
  backend=software fallback=none material= theme=aetheric_dark
  source=e13114ec328cce00747dec8565b1188a3e2f920817661d2c41bb4a347e0463cd
```

followed by:

```
[wm-frame] window-degraded window_id=1 reason=unresolved-or-duplicate-content
```

**The frame rendered successfully.** `status=engine2d_rendered`,
`backend=software` (not `native-safe-fallback`), `fallback=none` meaning no
degradation was needed. It is rejected purely on provenance metadata.

`wm_content_frame_web_provenance_valid` (`src/lib/common/ui/window_scene.spl`,
grep the fn name) requires all of the following for a
`WM_CONTENT_ORIGIN_SIMPLE_WEB` frame. Checked against the observed line:

| condition | observed | ok |
|---|---|---|
| `engine2d_status == "engine2d_rendered"` | yes | ok |
| `engine2d_backend != ""` | `software` | ok |
| `engine2d_backend != "native-safe-fallback"` | `software` | ok |
| `material_fallback_kind == "solid-material"` | **`none`** | **FAIL** |
| `material_fallback_reason != ""` | not printed | unknown |
| `material_fallback_sha256.len() == 64` | **empty** | **FAIL** |
| `theme_id != ""` | `aetheric_dark` | ok |
| `theme_source_manifest_sha256.len() == 64` | 64 hex | ok |

Both failures have one source: `_simple_web_realized_material_fallback`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
grep the fn name) returns `WebRenderMaterialFallbackProvenance.none()` when
`material_count == 0`, and `.none()` carries an empty kind and empty sha256.

**So exactly one thing is wrong: no node was counted as having realized a solid
material.** Everything downstream is that one fact reported twice.

## The gate is not over-strict here

Two gates on this harness *were* over-strict earlier today (the ELF64
assertion on a deliberately-ELF32 multiboot image; the fsck warning-vs-error
conflation). **This one is different and should not be relaxed.** The
provenance chain exists to prove the theme's backdrop was actually realized
when backdrop sampling is unavailable; issuing a digest for a frame that did
not realize the material would make the evidence meaningless. Fix the producer.

## What is verified, and what is not

**Verified:** the annotation IS emitted. `simple_web_window_renderer.spl` (grep
`data-wm-theme-fallback`) wraps every window body:

```
<div class='wm-app-content' data-wm-theme-fallback='solid-material'
     data-wm-theme-bg='{solid_css}' data-wm-theme-fg='{text_css}'>
```

**Verified:** the realization step exists and looks correct — on
`data-wm-theme-fallback == "solid-material"` it applies
`backdrop-filter:none;-webkit-backdrop-filter:none;background-image:none;` plus
`background-color:<wm_bg>` and `color:<wm_fg>` via `apply_decls`, *after* the
normal cascade (grep `data-wm-theme-bg` in the layout renderer, ~line 6015).

**NOT established:** why `declared_realized` is nonetheless false. It requires
all five of:

```
declared        - attr == "solid-material"                  (emitted; should hold)
declared_bg     - parse_color_alpha(data-wm-theme-bg) != 0
bg_alpha        - (styles[i].bg >> 24) & 255 == 255
bg match        - styles[i].bg == declared_bg
layers_cleared  - background_gradient_from == 0 and background_gradient_to == 0
                  and bg_layers_raw == ""
```

Narrowing done so far: `bg_layers_raw` is **only ever read, never assigned**
outside the `Style` constructor default of `""` — it is declared at
`simple_web_html_layout_renderer.spl:1746` and read at two provenance sites
(`:9309`, `:9734`) and nowhere else. If it is genuinely never written, it
cannot be the failing term, which points at `styles[i].bg == declared_bg` (a
color-space / parse mismatch between `_theme_rgb_css(_theme_solid_fallback_rgba(theme))`
and the computed `background-color`) or at the gradient stops.

**Do not fix on this inference.** The cheap decisive step is to print the five
terms for the annotated node and see which is false, rather than reasoning
further about the cascade. `_simple_web_realized_material_fallback` is the right
place for that probe, and per the log-retention rule it should go in
level-gated rather than be deleted afterwards.

## Reproduction

```sh
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
grep -a 'content-provenance-rejected' build/simpleos_wm_fullscreen_evidence/serial.log
```

Run takes ~10 min (kernel rebuild + QEMU boot).

## Harness landmine: the source-revision guard races parallel sessions

A first run of this harness failed with a *different* reason:

```
simpleos_wm_fullscreen_kernel_build_status=source-changed-cache-preserved
simpleos_wm_fullscreen_reason=wm-simple-web-build-source-changed
```

`kernel_source_revision()` hashes every `*.spl/*.c/*.h/*.s/*.S/*.ld` under
`src/os`, `src/lib`, `build/os/generated`, and
`examples/09_embedded/simple_os/arch/x86_64` **before and after** the build, and
fails if they differ. This is a correct guard — it refuses to admit an artifact
that does not match its recorded revision — but it means **any VCS operation
during the ~10-minute build fails the run**. In that instance a `jj rebase` and
`jj workspace update-stale` ("modified 4 files") were run concurrently by this
session; nothing was wrong with the cell.

Before a run, confirm the tree is quiescent, and do not touch VCS during it:

```sh
snap() { find src/os src/lib build/os/generated \
  examples/09_embedded/simple_os/arch/x86_64 -type f \
  \( -name '*.spl' -o -name '*.c' -o -name '*.h' -o -name '*.s' \
     -o -name '*.S' -o -name '*.ld' \) -printf '%p %s %T@\n' \
  | LC_ALL=C sort | sha256sum | cut -c1-16; }
snap; sleep 45; snap    # must match
```

With 5 parallel jj processes live on this repo, this is a real and recurring
failure mode, not a one-off.
