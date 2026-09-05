# SimpleOS-WM cell: frame renders correctly but is rejected — `material_fallback_kind=none`, empty material digest

- **ID:** simpleos_wm_content_provenance_material_fallback_none_2026-07-25
- **Status:** OPEN — pending re-run; the suspected cause was fixed upstream (5a01603505b, fd935c8d9ad) after the analysed run
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
normal cascade (grep `data-wm-theme-bg` in the layout renderer).

**NOT established at the time of the failing run:** why `declared_realized` was
false. The predicate then required all five of:

```
declared        - attr == "solid-material"                  (emitted; should hold)
declared_bg     - parse_color_alpha(data-wm-theme-bg) != 0
bg_alpha        - (styles[i].bg >> 24) & 255 == 255
bg match        - styles[i].bg == declared_bg
layers_cleared  - background_gradient_from == 0 and background_gradient_to == 0
                  and bg_layers_raw == ""
```

Narrowing at the time: `bg_layers_raw` appeared to be read-only (never assigned
outside the `Style` constructor default of `""`), pointing suspicion at
`styles[i].bg == declared_bg` — a mismatch between
`_theme_rgb_css(_theme_solid_fallback_rgba(theme))` and the computed
`background-color`.

### SUPERSEDED — another session removed that exact term

Do **not** act on the narrowing above. Between the failing run and this note,
two commits landed on the renderer:

```
5a01603505b fix(web): align material fallback provenance
fd935c8d9ad fix(web): diagnose freestanding fallback predicate
```

The predicate is now the shared, exported
`simple_web_material_fallback_realized(declared, bg, gradient_from, gradient_to, layers_raw)`
— and the `styles[i].bg == declared_bg` re-parse is **gone**. The in-code
rationale states that re-parsing `data-wm-theme-bg` and demanding a second
exact equality "made this parallel provenance path reject the already-executed
opaque material on freestanding x86 even though the Draw IR command recorded
solid-material and its image layers were cleared."

That is the same defect class this file described, fixed at the source. A
level-gated rejection receipt now also exists, so the five terms no longer need
a hand-added probe — grep the serial log for `[web-material-fallback] rejected`
and it prints `declared`, `bg`, `bg_alpha`, `gradient_from`, `gradient_to`,
`layers_len`, `layers_cleared` directly.

**The serial log analysed above predates both commits** (zero occurrences of
`web-material-fallback` in it). This bug therefore needs a re-run against
current `main` before any further work — the observed rejection may already be
fixed.

> **Cite by marker, not line number.** An earlier revision of this file gave
> line numbers in `simple_web_html_layout_renderer.spl` (`:1746`, `:9309`,
> `:9734`, `~6015`). That file was **9,900 lines when those were written and is
> now 472** — a parallel session split it, invalidating every one of them in a
> single commit. All references here are grep markers instead. Same lesson as
> `simpleos_x86_64_kernel_links_as_elf32_em386_2026-07-25.md`.

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

## RESOLVED (diagnosis) 2026-07-26 — root cause is a collapsed HTML parse in the guest, not provenance

Three hypotheses were on the table: (a) the WM frame does not go through the
wrapping function that emits `data-wm-theme-fallback`; (b) `attr_value` fails to
find the attribute when `class=` is the first attribute; (c) the freestanding
guest build lowers this path differently than the host.

**(c) is true. (a) and (b) are both refuted with evidence.**

### Refuting (a)

`os.compositor.simple_web_window_renderer.simple_web_content_full_html_with_theme`
was run on the host for the exact production window. The emitted document does
carry the contract, with `class=` first exactly as suspected:

```
...<body><div id="app"><div class='wm-app-content'
  data-wm-theme-fallback='solid-material' data-wm-theme-bg='#1F1F21'
  data-wm-theme-fg='#E4E2E4'>...
```

The guest path is also confirmed to reach the reducer:
`os.desktop.shell.runtime_content_frames` -> `simple_web_content_frame_cached`
-> `simple_web_content_render_request_with_theme` ->
`WebRenderPixelArtifactCache.request_to_pixel_artifact` ->
`SimpleWebEngine2DStaticPixelCache.result_for_html` ->
`simple_web_layout_render_html_readback_engine2d_result` ->
`simple_web_layout_render_html_draw_ir_result` ->
`_simple_web_realized_material_fallback`. Every branch of that chain propagates
`material_fallback`.

### Refuting (b), and the actual root cause

A permanent shape receipt was added to `_simple_web_realized_material_fallback`
(fires whenever `material_count == 0`). The guest reports:

```
[web-material-fallback] none nodes=1 styles=1 attr_nodes=0 declared_nodes=0 rejected=0
[web-layout]  degenerate-parse html_len=5794 nodes=1 split_parts=18
```

`nodes=1` is the `#root` node alone: **`parse_html` produces no element nodes at
all for a 5794-byte document in the freestanding SimpleOS x86_64 kernel build.**
`attr_nodes=0` (a raw substring scan, not `attr_value`) proves the contract node
is absent from the parsed DOM entirely, so attribute ordering and `attr_value`
are not implicated — (b) is refuted.

The provenance gate is therefore CORRECT and must not be relaxed: it is
fail-closing on a genuinely empty DOM. The frame still reports
`engine2d_rendered` only because an empty DOM still paints a canvas.

The collapse is inside `parse_html` / `_html_scan_events`, downstream of
`text.split`: `html.split("<")` returns 18 parts, which is plausible for this
document (its ~5 KB `<style>` block contains no `<`), yet `_html_scan_events`
yields zero node-making events. `parse_html` has no budget guard, so this is not
a deadline bail.

### Second, independent freestanding defect found: omitted default arguments

`extract_css_vw(html, viewport_w, trace_stages: bool = false)` was emitting its
`trace_stages` receipts in the guest:

```
[layout-trace] css_scan candidates=0 declarations=0 wrappers=0
[layout-trace] css_result rules=0 decls=0
```

The only caller that passes `trace_stages=true` is
`simple_web_layout_render_html_software_pixels_traced`, and none of its earlier
prints (`parse_html_ms`, `extract_css_ms`, ...) appear in the log, so it never
ran. `compute_styles`, called on the same path with an explicit `false`, stayed
silent. Passing the argument explicitly made the spurious receipts disappear.

So **an omitted trailing default argument materializes as a non-default
(truthy) value in this build.** All `extract_css_vw` / `compute_styles` call
sites in the two renderer files now pass every parameter explicitly.

### Where the fix belongs

Not in the renderer and not in the gate. Two freestanding
codegen/runtime defects need fixing:

1. `parse_html` / `_html_scan_events` produce no element nodes for a valid
   document (host produces a full DOM for the identical string).
2. Omitted default arguments do not receive their declared default.

Until (1) is fixed, `SimpleOS-WM x QEMU` stays `reason=guest-render-fault` with
`fallback=none`, and that verdict is honest.
