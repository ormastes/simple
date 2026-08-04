# Vulkan engine2d lane publishes a TRUNCATED frame as a proven device frame when the font route fails

**Date:** 2026-08-02 (mechanism re-pinned 2026-08-04)
**Status:** OPEN — mechanism pinned by reading + A/B probes; fix not applied
**Severity:** High (silent wrong frame, exit 0, `render_degraded=false`,
`readback.source=device_readback`)
**Lane:** engine2d backend `"vulkan"` under
`web_render_backend("pure_simple", W, H).render_html_to_pixels(html, "vulkan")`.

## Verdict (2026-08-04 A/B, 96x72, same document, same binary)

**The vulkan lane does NOT drop draws.** A text-free document paints
bit-identically on both backends. The truncation is triggered by TEXT, and its
mechanism is a latch that survives the font failure and silently no-ops every
later primitive while the readback still reports a proven device frame.

Text-free A/B (`textfree_ab_probe.spl`, 96x72, five absolutely-sized boxes on a
body background, NO text nodes anywhere, `# @exec_limit 2000000000`, budget
floor 900000ms). Verbatim (`textfree_ab.log`):

```
sw_len=6912       vk_len=6912
sw_body=4728      vk_body=4728
sw_blue=504       vk_blue=504
sw_green=504      vk_green=504
sw_amber=504      vk_amber=504
sw_red=336        vk_red=336
sw_purple=336     vk_purple=336
[vk-font-lane] readback source=device_readback pixels=6912 completion_unknown=false cpu_fallback_reason=
textfree_probe_done
exit=0
```

Every box matches exactly, and the instrumented receipt confirms the frame came
back as a genuine `device_readback` with the latch clear. Compare the same
document WITH text on the same lane and binary (prior session, `probe_vk96.log`
/ `probe_sw96.log`, 96x72):

| box | software (with text) | vulkan (with text) | vulkan (text-free) |
|-----|---------------------|--------------------|--------------------|
| blue | 504 | **0** | 504 |
| green | 504 | **0** | 504 |
| amber | 504 | **0** | 504 |
| pulse red | 240 | **0** | 336 (box-d) |
| body bg | — | 5376 | 4728 |

So: rects are fine; text poisons the rest of the frame. The earlier framing
("drops all draws after two rect fills") was the *symptom*; the defect is that a
**failed/incomplete font route publishes a partial frame as if it were
complete**, instead of failing closed or falling back honestly.

## Mechanism (file:line, pinned by reading)

Two cooperating sites turn one font-route failure into a silently truncated,
fully "proven" frame:

**(A) The font route rolls the device framebuffer BACK to its pre-text state.**
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl:462, 467, 472, 478,
499, 519` — on every non-parity / non-promotable outcome
`_composite_font_batch_impl` calls
`vulkan_sffi_copy_to_buffer(framebuffer, before_bytes, 0)`, restoring the
snapshot taken at line 376 before any glyph dispatch. That is a legitimate
"undo my partial writes", and it is why the device framebuffer that comes back
contains exactly the commands that document-order PRECEDE the first text
command.

**(B) The poison latch silently no-ops every later primitive, and the CPU
fallback surface it installs is never drawn into.**
`src/lib/gc_async_mut/gpu/engine2d/engine.spl:325-337`
(`_poison_vulkan_font_surface`, reached from `engine.spl:1467` when
`composite_font_batch` returns one of `partial-framebuffer-restore-failed`,
`missing-command-cleanup-capability`, `descriptor-cleanup-failed`,
`atlas-cleanup-failed`, `fence-completion-unknown`, `device-lost`,
`fence-cleanup-failed`, `fence-wait-evidence-failed`, `cleanup-failed`):

```
me _poison_vulkan_font_surface(fallback_pixels: [u32]):
    if val Some(vulkan) = self.vulkan_backend:
        vulkan.mark_completion_unknown()        # engine.spl:327
        self.vulkan_backend = Some(vulkan)      # engine.spl:328  <-- STAYS Some
    ...
    self.backend = software                     # engine.spl:334
    self.selected_backend_name = "vulkan-poisoned-software"   # engine.spl:336
    self.vulkan_font_state_unknown = true       # engine.spl:337
```

The intent is clear — install a CPU surface seeded with the last good pixels and
keep rendering there. It does not work, because **all 37 primitive routers in
`Engine2D` test `elif val Some(vulkan) = self.vulkan_backend:` BEFORE the
`else: self.backend` arm** (e.g. `draw_rect_filled` at
`engine.spl:1127-1143`, dispatch at 1138; `draw_rect` at 1120; `draw_line` at
1159; `draw_text` at 1550). `self.vulkan_backend` is still `Some`, so every
subsequent box rect is dispatched to the *poisoned* vulkan backend — whose
methods all begin `if self.completion_unknown: return`
(`backend_vulkan.spl:964, 979, 986, 1034, 1044, 1054, 1063, 1072, 1095, 1131,
1412, 1416, 1420, 1424, 1428, ...`). Each is a **silent no-op returning no
status**. The software fallback surface installed at `engine.spl:334` is dead
code: nothing ever draws into it. Nothing keys off
`selected_backend_name == "vulkan-poisoned-software"` except `shutdown()`
(`engine.spl:2737`).

**Result.** Readback goes through
`draw_ir_target_read_pixels_with_source` (`engine.spl:2697`), which likewise
tests `elif val Some(vulkan) = self.vulkan_backend:` first, and returns the
device framebuffer — which (A) restored to its pre-text content and (B) then
froze. Provenance is fully green: `device_readback`, positive backend handle and
device identity, full `pixel_count`, `render_degraded=false`, material fallback
`none/not_requested`, and `skipped_command_count` does NOT count the dropped
primitives (they were "dispatched", they just no-op'd). Prior-session receipt
(`vk96_readback.log`, verbatim):

```
rb_source=device_readback
rb_backend_handle=1
rb_device_identity=135996263371264
rb_pixel_count=6912
rb_degraded=false
rb_mf_kind=none
rb_mf_reason=not_requested
rb_count_body_bg=5376
rb_count_box_blue=0
rb_count_box_green=0
rb_count_box_amber=0
```

This REFUTES the earlier `completion_unknown`-empty-readback hypothesis: that
path (`backend_vulkan.spl:1372-1373`,
`return engine2d_readback([], "completion_unknown")`) yields an EMPTY buffer,
which a caller can detect. The observed failure is worse — a full-length,
positively-attested device frame that is missing most of its content.

## Reproduction

```
SP=<scratchpad>; cd /home/ormastes/dev/pub/simple
# A: text-free -- vulkan == software, all boxes (this is the control)
SIMPLE_TIMEOUT_SECONDS=3600 SIMPLE_EXECUTION_MODE=interpreter \
  bin/simple run $SP/textfree_ab_probe.spl
# B: same CSS/structure WITH text -- vulkan box counts drop to 0
SIMPLE_TIMEOUT_SECONDS=3600 SIMPLE_EXECUTION_MODE=interpreter \
  bin/simple run $SP/text_axis_lane_probe.spl
```

Both probes carry `# @exec_limit 2000000000` and arm
`simple_web_layout_set_render_budget_floor_ms(900000)`. The with-text vulkan arm
spends many minutes in the interpreted glyph route before the paint phase; that
grind is a separate cost issue (contention-inflated on a loaded box), NOT the
defect — `[web-phase] phase=paint elapsed_ms=306..340` for the truncated frame
is comparable to the software lane's FULL paint (377ms).

## Hypotheses eliminated (prior session, all under
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`, release-seed binary)

- **stale module source / different renderer copy** — refuted: same binary, same
  source paints fully on `"software"` and on the text-free vulkan lane.
- **budget-floor setter no-op** — refuted: style pass ran 18.4s past the 10s
  default with no `budget-break`, `style_end` reached, `render_degraded=false`;
  an `SIMPLE_WEB_RENDER_BUDGET_MS=900000` env control behaved identically.
- **fallback style producer (element selectors only)** — refuted: the
  heuristic fast path routes any doc with `<h1>`/`<p>` to the real renderer
  (`simple_web_engine2d_renderer.spl:~1064`); `[web-phase]` shows
  parse -> style(12 nodes) -> layout -> compose_shaping all complete.
- **membership/`.contains` untagged-key defect** — not implicated
  (`membership_run.log`).
- **vulkan RECT execution** — refuted twice: `rect_only_lane.log` (64x48) and
  the 96x72 `textfree_ab.log` above both show vulkan == software exactly.

## Why `bin/simple test` paints the showcase

`"vulkan"` resolves through `Engine2D.probe_backend`
(`simple_web_engine2d_resolved_backend_name`); when the probe does not come back
Initialized the lane silently becomes `"software"`, which paints correctly, and
`web_showcase_full_gpu_offload_spec.spl` explicitly tolerates a non-device
readback. So the green 13/13 spec never executes the defective path.

## Fix direction

Standing policy: GPU-first with an HONEST CPU fallback — a lane that cannot
complete must fall back and say so, never publish a truncated frame.

1. **Make the poison latch actually reroute.** `_poison_vulkan_font_surface`
   installs a software surface but leaves `self.vulkan_backend = Some(...)`, so
   the 37 `elif val Some(vulkan) = self.vulkan_backend:` routers keep dispatching
   into the dead backend. The routers must fall through to `self.backend`
   whenever `self.vulkan_font_state_unknown` is set (equivalently when
   `selected_backend_name == "vulkan-poisoned-software"`). NOTE: simply setting
   `self.vulkan_backend = nil` is NOT correct — `shutdown()` (`engine.spl:2737`)
   needs that handle to release/quarantine the device resources. The gate
   belongs in the routers (or in one shared dispatch helper), not in the handle.
2. **Fail closed on the readback.** `draw_ir_target_read_pixels_with_source`
   (`engine.spl:2697`) must not return `device_readback` provenance for a frame
   assembled while `vulkan_font_state_unknown` was latched. Downgrade it to
   `cpu_fallback` with the poison reason attached so
   `simple_web_layout_material_provenance_after_backend_execution` can attribute
   the loss, mirroring `_simple_web_layout_draw_ir_with_degraded_retry`
   (`simple_web_layout_engine2d_fast.spl:290`).
3. **Count what was dropped.** A no-op'd primitive must increment
   `skipped_command_count`; today it is invisible, which is what let a truncated
   frame report a clean device render.
4. **Root-cause the font failure itself.** Separately, find which dispatch in
   `_composite_font_batch_impl` fails under the interpreter (fenced submission,
   SPIR-V glyph pipeline, or descriptor cleanup) — items 1-3 make the failure
   honest, they do not make the text render.

## Probe artifacts (scratchpad)

- `textfree_ab_probe.spl` / `textfree_ab.log` — **the decisive A/B**, 96x72,
  text-free, vulkan == software on all five boxes, `device_readback`,
  `completion_unknown=false`
- `text_axis_lane_probe.spl` / `text_axis_lane.log` — 96x72, empty-text full
  paint vs real-text truncation
- `rect_only_lane_probe.spl` / `rect_only_lane.log` — 64x48 rect-only control
- `probe_sw96.log` / `probe_vk96.log` — 96x72 with-text software vs vulkan
- `vk96_readback.log` — provenance receipt for the truncated with-text frame
- `probe_releaseseed_run.log` — 320x240 with phase traces
