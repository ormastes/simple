# WM rung-(d): every text Draw IR command skipped — `config.language` reads `normal` instead of `und`

Status: ROOT-CAUSED, fix written in the working copy, **NOT LANDED** — the
confirming gate run had not produced a verdict when this was written. Nothing
here may be read as a rung-(d) pass. The four rung-(d) questions (capture
reached? `scanout_capture_size`? non-uniform PPM? verdict string?) are
UNANSWERED. Landing is blocked until `check-simpleos-wm-fullscreen-evidence.shs`
reports `skipped=0` with a pixel-variance-verified non-uniform PPM.
Lane: SimpleOS WM fullscreen, QEMU + OVMF pflash only. No board claim is made here.

## Symptom

The WM boots fully and reaches every readiness receipt —
`[production-readiness] wm=live renderer=engine2d`, `[scanout-evidence]`,
`[font-evidence]`, `[wm-loop] polling-active`. It then renders 12 of 20 Draw IR
commands and skips 8. The 8 skipped commands are exactly the text ones. Serial
shows, once per skipped command:

```
[font-select] no-candidate family='auto' category='auto' language='normal' script='auto'
[e2d-batch] selection-unsupported text_len=11 advances=11
[wm-frame] frame-degraded degraded_window_count=3 skipped=8 rendered=12 reason=unsupported Draw IR commands skipped: text-font-batch
```

## What the value actually is

`_font_render_config_default_selection` (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:582`)
requires `font_render_config_normalize(config.language) == "und"`. The config
carries `"normal"`, so default selection is refused; `_font_render_config_candidate`
then finds nothing (`"normal"` is not a language in the CLDR rank table) and
`font_render_config_selection_supported` returns false, skipping the batch.

Note which gates *passed*: `font_render_config_valid` accepted the same config
(no `[font-select] config-invalid` receipt, and `font_execution_plan_into`
returned `plan_count > 0`). That validator only checks
`config.language.trim() != ""` (`font_types.spl:146`) — it never checks the
sentinel — which is why a corrupt language survives validation and only trips
selection.

## The CSS-sentinel theory is wrong

The obvious hypothesis is that CSS `font-language-override: normal` — the CSS
initial value meaning "no override" — leaks into the font layer, whose "no
language" sentinel is the BCP-47 `und`. It does not:

- `_html_text_language` (`simple_web_html_layout_renderer_style.spl:299-312`)
  **already** maps the CSS spelling: `if override != "" and override.lower() != "normal"`,
  otherwise it walks ancestor `lang` attributes and finally returns `"und"`.
  The CSS boundary is correct as written and needs no change.
- That function's result feeds `resolve_font_metrics_with_language`, a *metrics*
  path. It is never assigned to `FontRenderConfig.language`.
- A repo-wide sweep for `FontRenderConfig(` finds exactly three production
  construction sites — `font_types.spl:285`, `engine.spl:166`, `engine.spl:1698`
  — and **all three spell `language: "und"`**. There is no production write of
  `.language` anywhere (`grep -rn '\.language *=' src/lib` returns only
  comparisons). No CSS spelling can reach this field.

So `"normal"` is not propagated from anywhere. It is manufactured.

## Root cause

`engine2d_default_font_config_for` (`src/lib/gc_async_mut/gpu/engine2d/engine.spl:162`)
had two exits:

```
val base = FontRenderConfig.default_for_size(font_size)
if not force_cpu_target:
    return base                       # hosted lane — text renders correctly
FontRenderConfig(                     # baremetal lane — text is skipped
    family: base.family, category: base.category, language: base.language,
    script: base.script, size: base.size, weight: base.weight, style: base.style,
    ... )
```

`force_cpu_target` is `self.baremetal_backend != nil`, so **the eleven-field
cross-struct copy is the only code the WM lane executes that the working hosted
lane does not.** That copy delivered `language = "normal"` — the value carried by
the `weight`/`style` slots — while `family`, `category` and `script` copied
correctly, which is exactly the shape the serial receipt reports.

This is the same freestanding entry-closure codegen family already documented and
worked around three times in `font_types.spl` (mixed boolean chains, lines
133-137 and 570-577), once for instance-method dispatch (`font_types.spl:99-105`),
and once for enum field equality (`font_types.spl:163-168`). The failing
construct differs — here it is field reads off another struct in a constructor
argument list — but the lane and the failure mode (a silently wrong value, no
diagnostic) are identical.

## Fix

Literal-initialize the `force_cpu_target` config instead of copying field-by-field
from `base`. Every value is already a compile-time constant in
`font_render_config_default_for_size`; only `size` (the parameter) and the pinned
`execution_target: "cpu"` differ from that function, so the rewrite is
value-identical on a healthy compiler and removes all eleven field reads.

The predicate at `font_renderer.spl:582` was deliberately **not** touched.
Teaching it to accept `"normal"` would have made the gate go quiet while leaving
the corrupt copy in place, and would have masked genuine misconfiguration —
`und` is the correct BCP-47 sentinel and `normal` is a CSS-only spelling that has
no business in the font layer.

## Gate evidence (2026-08-11) — rung (d) NOT reached, blocked EARLIER

Two runs of `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`, QEMU +
OVMF pflash, `SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT_SECONDS=3600` /
`..._WORKER_TIMEOUT_SECONDS=3400`.

**Run 1 (05:18:19Z) — contention, not a product result.**
`simpleos_wm_kernel_input_verdict=FAIL — kernel input source changed during
build (1515 file(s) hashed)`, `reason=wm-simple-web-build-source-changed`,
`kernel_build_attempts=3`, `serial_log_bytes=0`, no kernel, no disk image.
Concurrent sessions edited the kernel source closure mid-build. Discarded.

**Run 2 (05:33:43Z) — trustworthy input, but a different blocker.**
`simpleos_wm_kernel_input_verdict=PASS — 1515 file(s) hashed
(set=closure+linked-symbol-repair,
revision=ecca3da03633abb2a27a4b0f6deafa01f520dedac29a3c17f9c6a2c08d55951e)`.
Kernel, disk image and browser demo all built and staged (`pass`). Then:

| question | answer |
|---|---|
| reached capture? | **no** |
| `scanout_capture_size` | **0** |
| PPMs non-uniform? | **no PPMs at all** — `baseline.ppm`, `fullscreen.ppm`, `restored.ppm`, `browser-event.ppm` all `file_status=missing`, `bytes=0`. Pixel variance not runnable. |
| verdict | `simpleos_wm_fullscreen_status=fail` / `simpleos_wm_fullscreen_reason=dynamic-scanout-or-desktop-readiness-missing` |

The guest never started the WM. Serial ends at:

```
[vfs-init] file chain read complete first_cluster=88253 clusters=39 bytes=79160 requested=79160
[heap] alloc sz=0x200000 off_before=0xbf12660 caller=0x800dc7c
[PANIC] heap exhausted
[PANIC] heap_off=0xbf12660 req=0x200000 limit=0xc000000
```

The guest heap is at 0xbf12660 of a 0xc000000 limit — **99.6% consumed by asset
loading** — and dies on the next 2 MiB request, during `vfs-init`, before any
render code. There are **zero** `font-select` / `frame-degraded` /
`selection-unsupported` receipts in the whole log, and no
`[production-readiness] wm=live`.

**So this run does not exercise the text defect at all**, and says nothing about
whether the fix above works. It is a new, earlier blocker sitting in front of
rung (d).

**Attribution — two variables moved, not one.** The last run that reached
`wm=live` (05:04Z, `reason=guest-render-fault`, the frame-degraded/skipped=8
baseline) hashed **1514** kernel input files and contains **zero** `PANIC`
lines. Run 2 hashed **1515** — another session added a file to the kernel source
closure — *and* carried this fix. The fix is almost certainly not the cause: it
is a value-identical constructor rewrite whose only caller is `draw_text*`, no
text was ever drawn (zero receipts), the panic precedes all rendering, and four
lines of constructor cannot account for ~191 MiB of heap. But with two variables
moved this is an argument, not a measurement, and it is recorded as such.

## Follow-ups

- The underlying codegen defect is unfixed; only this call site is worked around.
  Any other cross-struct field-read constructor on the freestanding entry-closure
  lane is a latent instance of the same bug.
- `font_render_config_valid` does not validate the language sentinel, so a corrupt
  language reaches selection before anything complains. Tightening it would have
  caught this one gate-run earlier.
