# Vulkan engine2d lane publishes a TRUNCATED frame as a proven device frame when the font route fails

**Date:** 2026-08-02 (mechanism re-pinned 2026-08-04; **FIXED 2026-08-04**)
**Status:** **FIXED** — see "Fix (2026-08-04, second attempt) — the write-back"
at the END of this file. Mechanisms (A) and (B) named in the body below are both
REFUTED; the third correction pinned the real one (a lost value write-back) and
the fix removes it. Read the correction sections at the END of this file BEFORE
anything above them:

1. "Correction (2026-08-04): the poison latch is NOT the mechanism" — refutes
   mechanism (B). A router-gate hardening landed in `28288f98102`; it is a real
   fix for a real separate path, but it did not change this bug.
2. "Second correction (2026-08-04): mechanism (A) refuted, and the REAL
   mechanism measured" — refutes mechanism (A) (**no restore ever fires; the
   font composite PROMOTES**) and pins what actually drops the primitives.
   Everything in the Mechanism section below is now known to be wrong for this
   document; it is kept only so the refutations have something to point at.

Do not re-derive either theory. The instrument is `SIMPLE_VK_ORDER_TRACE=1` —
see the second correction for what it prints and what it measured.
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

### Same-run with-text A/B (64x48, `vulkan_drop_probe.spl` / `.log`, this session)

Both arms in ONE process, one binary, one document (`<h1>Hi</h1>` plus three
absolutely-sized boxes). Verbatim:

```
sw_len=3072     vk_len=3072
sw_body=1656    vk_body=2304
sw_h1=742       vk_h1=742
sw_blue=216     vk_blue=0
sw_green=216    vk_green=0
sw_amber=216    vk_amber=0
probe_done
```

The arithmetic pins the loss exactly:

- `2304 - 1656 = 648 = 3 x 216` — every box pixel came back as **body
  background**, i.e. the three box rects never landed. Not garbage, not a short
  buffer: the frame is full-length (3072) and internally consistent.
- `vk_h1 == sw_h1 == 742` — the h1 background rect, which document-order
  PRECEDES the text command, painted identically on both lanes.
- Both arms account for the same 3046 pixels, leaving the same ~26 glyph pixels
  inside the h1 band on both lanes — so on this document the glyphs themselves
  did land on the vulkan arm (through the CPU suffix of the font plan). **The
  loss is confined strictly to the commands that FOLLOW the text draw**, which
  is precisely the poison-latch signature described below, not a font-rendering
  failure.

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

- `vulkan_drop_probe.spl` / `vulkan_drop_probe.log` — **same-run with-text
  A/B**, 64x48, both backends in one process; box pixels revert to body bg on
  vulkan while the pre-text h1 rect and the glyphs match software exactly
- `textfree_ab_probe.spl` / `textfree_ab.log` — **the decisive A/B**, 96x72,
  text-free, vulkan == software on all five boxes, `device_readback`,
  `completion_unknown=false`
- `text_axis_lane_probe.spl` / `text_axis_lane.log` — 96x72, empty-text full
  paint vs real-text truncation
- `rect_only_lane_probe.spl` / `rect_only_lane.log` — 64x48 rect-only control
- `probe_sw96.log` / `probe_vk96.log` — 96x72 with-text software vs vulkan
- `vk96_readback.log` — provenance receipt for the truncated with-text frame
- `probe_releaseseed_run.log` — 320x240 with phase traces

## Correction (2026-08-04): the poison latch is NOT the mechanism

**The fix below landed (`28288f98102`) and did NOT fix this bug.** It is kept
because it is a real hardening of a real (separate) silent-drop path, but the
mechanism section (B) above is REFUTED for this document, and this bug is still
open. The refutation is clean, and it is worth stating precisely because it
turns the landed change into a *falsification instrument*:

The landed `read_pixels_with_source()` returns
`engine2d_readback(..., "cpu_fallback")` **unconditionally** whenever
`vulkan_font_state_unknown` is true. So on the fixed tree the string
`device_readback` is *impossible* for a poisoned lane. Post-fix run, gate
verified present in the source immediately before AND after the run
(`PRECHECK=31 POSTCHECK=31`), `withtext_ab_probe.spl`, 96x72, verbatim:

```
sw_source=cpu_mirror   sw_blue=504 sw_green=504 sw_amber=504
vk_source=device_readback
vk_degraded=false
vk_backend_handle=1
vk_pixel_count=6912
vk_body=5376
vk_blue=0  vk_green=0  vk_amber=0
Results: FAIL-silent-partial sw_boxes=504/504/504 vk_boxes=0/0/0 vk_source=device_readback vk_degraded=false
```

and the 64x48 same-run A/B, also post-fix, reproduces the pre-fix numbers
*exactly* (`vk_body=2304 vk_h1=742 vk_blue=vk_green=vk_amber=0`).

That 64x48 result was **independently replicated twice** — two separate
post-fix runs (`vulkan_drop_v2.log`, `vulkan_drop_v3.log`), each with the gate
re-grepped present in the source immediately before AND after the run
(`PRECHECK=31 POSTCHECK=31` both times), producing byte-identical counts. The
falsification is not a single flaky run, and it is not a stale-source artifact:
the standing hazard in this tree is that a parallel sync silently reverts the
working copy mid-session (it did so three times while this fix was being
verified), which is exactly why both runs bracket themselves with a source
check. Any future attempt on this bug should do the same — an unbracketed run
here cannot distinguish "the fix didn't work" from "the fix wasn't there".

Therefore:

1. **`vulkan_font_state_unknown` was FALSE.** `_poison_vulkan_font_surface`
   never ran for this document, so the "all routers keep dispatching into the
   poisoned backend" story in (B) cannot be what drops the boxes. The poison
   list at `engine.spl:1455-1464` only fires for nine specific
   `evidence.reason` values; this document's font route evidently returns some
   other reason.
2. **The backend does not think it is degraded either.** `completion_unknown`
   would surface as source `completion_unknown`, and `cpu_fallback_used` as
   `cpu_fallback`. We got neither — a genuine `device_readback` with a positive
   handle and full pixel count.
3. So the box rects are dispatched to a Vulkan backend that believes it is
   healthy, and their writes still do not reach the framebuffer that is read
   back. That points at the **(A)** roll-back / submission-ordering axis, not
   at any latch: the surviving hypothesis is that the font route's
   `vulkan_sffi_copy_to_buffer(framebuffer, before_bytes, 0)` restore, or the
   pending-compute batch it leaves behind, lands AFTER the later primitives'
   writes at submit/flush time and overwrites them — which would explain
   exactly "everything document-order after the first text command is missing"
   while every receipt stays honest-looking.

**Next step for whoever picks this up:** instrument
`_flush_pending_compute` / `_enqueue_framebuffer_compute`
(`backend_vulkan_helpers.spl`) and the restore at
`backend_vulkan_font.spl:462,467,472,478,499,519` with submission-order and
generation counters, and check whether the restore's buffer copy is submitted
after the post-text rect dispatches. Do NOT re-derive the poison-latch theory:
the A/B above rules it out.

## Fix (2026-08-04) — landed, correct, but INSUFFICIENT for this bug

Landed as `28288f98102`. **It does not fix this bug** — see the Correction
above. What it does fix is a genuine, separate silent-drop path: *if* the
poison latch ever does fire, every later primitive used to be swallowed. That
path is now closed and, as a side effect, the readback provenance became a
usable probe (it is what falsified the mechanism). Kept on those grounds.

Applied where the mechanism section pinned it: at the router gate. The
`(A)` framebuffer roll-back in `backend_vulkan_font.spl` is left alone — it is a
legitimate "undo my partial writes"; the defect was `(B)`, that the roll-back
was then published as a complete frame.

### `src/lib/gc_async_mut/gpu/engine2d/engine.spl`

1. New `me _vulkan_primitive_target() -> VulkanBackend?` returns `nil` while
   `vulkan_font_state_unknown` is set, and `self.vulkan_backend` otherwise.
   Every primitive router now resolves its handle through it —
   `elif val Some(vulkan) = self._vulkan_primitive_target():`, **29 sites** on
   this revision (the "37" in the mechanism section above counted routers, not
   the distinct `elif` dispatch lines). A poisoned lane therefore falls through
   to `else: self.backend`, which is the CPU fallback surface
   `_poison_vulkan_font_surface` installs — so that surface stops being dead
   code and is actually drawn into.

   **Gate, do not null.** `self.vulkan_backend` itself is untouched, because
   `shutdown()` still needs the handle to release the device session; nulling it
   would leak.

2. `read_pixels_with_source()` returns
   `engine2d_readback(self.backend.read_pixels(), "cpu_fallback")` while the
   lane is poisoned. `device_readback` can no longer be reported for a frame the
   device did not produce — this is the receipt that was lying in
   `vk96_readback.log`.

3. `draw_text()`'s `if self.vulkan_font_state_unknown: return` is **removed**.
   It existed only to keep the router chain below it off the dead backend, which
   the gate now does; with it gone the chain falls through to the software
   surface and the bitmap text is painted rather than silently dropped.

4. `me vulkan_font_poisoned() -> bool` exposes the state to callers.

### `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`

5. `_simple_web_layout_execute_draw_ir_composition` latches `lane_demoted` — an
   accelerated `backend_name` whose readback came back `cpu_fallback` — into
   `render_degraded`. A demoted frame is no longer published as a clean one.

### On `skipped_command_count`

After (1)+(3) the poisoned lane drops nothing: primitives and the CPU font
plan's glyph blits all land on the fallback surface. The count is therefore
honest at 0 *by construction* rather than by omission, and no counter was added
— a counter that is always 0 would be new dead code.

One unaccounted text drop remains, orthogonal and pre-existing:
`draw_text_configured()` returns `false` (empty plan / unsupported selection)
without drawing and without incrementing anything, and `draw_ir_adv.spl:1722`
ignores that return. Separate follow-up, not part of this fix.

### Verification

- **Control — the healthy path must not move.** `textfree_ab_probe.spl`, 96x72,
  no text nodes: software vs vulkan stay bit-identical after the fix
  (`sw/vk_blue=504 green=504 amber=504 red=336 purple=336 body=4728`,
  `textfree_v2.log`). The source was re-grepped immediately before AND after the
  run (31 gate sites both times) so the result provably describes the fixed
  tree.
- **With-text A/B — FAILED, and that failure is the finding.**
  `vulkan_drop_probe.spl` (64x48) and `withtext_ab_probe.spl` (96x72) both
  reproduce the truncation unchanged on the fixed tree; the 96x72 arm emits
  `Results: FAIL-silent-partial ... vk_source=device_readback vk_degraded=false`.
  See the Correction section for why that verdict refutes the mechanism rather
  than merely reporting a miss.
- **Regression gate** — `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl`
  was started three times and never reached a `Results:` line (final status:
  `grep -c '^Results:' showcase_v3.log` = 0): run 1 was
  invalidated by a working-copy revert mid-run, runs 2 and 3 were killed
  (exit 144 / exit 1) under heavy parallel-session contention (6+ concurrent
  copies of this same spec were running). **Still owed.** The change is
  inert unless `vulkan_font_state_unknown` is set, and that spec's lane
  resolves to `"software"`, so the expected impact is nil — but that is an
  argument, not a measurement.

## Second correction (2026-08-04): mechanism (A) refuted, and the REAL mechanism measured

Mechanism **(A)** — "`_composite_font_batch_impl` snapshots the framebuffer at
`backend_vulkan_font.spl:376` and one of the six restores at
`:462/467/472/478/499/519` lands after the later rect draws" — is **REFUTED by
direct measurement**: on the failing run the font route does not restore
anything. It *succeeds*. **Zero `font-restore` lines are emitted**, and the
outcome is `status=promoted parity=true promotion_ready=true dispatched=2/2`,
which takes `:516 if result.promotion_ready: self.dirty = true` and skips both
terminal restores.

The real mechanism is one line further on and is now pinned.

### The instrument

`SIMPLE_VK_ORDER_TRACE=1` (level-gated, default OFF; one `env_get` per dispatch
when disarmed) prints `[vk-order]` submission-order receipts:

| line | site | answers |
|------|------|---------|
| `dispatch pipe= batched= rc= fb= pending_cmd= pending_n= clip_on= clip=` | `backend_vulkan_helpers.spl::_dispatch_framebuffer_checked` | which primitives reach the device, with what result and clip |
| `flush rc= dirty= cpu_fallback= completion_unknown=` | `..._helpers.spl::_flush_pending_compute` | every batch submission outcome (all 8 return paths, via a traced wrapper over `_flush_pending_compute_impl`) |
| `image-composite x= y= w= h= mode= rc= fb=` | `backend_vulkan.spl::_draw_image_composite_native` | glyph/image blits |
| `readback-entry dirty= pending_cmd= pending_n= cpu_fallback= completion_unknown= fb=` | `backend_vulkan.spl::read_pixels_with_source` | backend state at readback |
| `font-snapshot` / `font-restore site=<six named sites>` / `font-done` | `backend_vulkan_font.spl:376 / 462,467,472,478,499,519 / end of impl` | whether the snapshot and each restore fire, and the outcome |

### The failing run, verbatim (`vulkan_drop_probe.spl`, 64x48, vulkan arm)

```
730  dispatch pipe=1 rc=1  pending_cmd=1 pending_n=1     # clear
731  dispatch pipe=2 rc=1  pending_cmd=1 pending_n=2     # rect
732  dispatch pipe=2 rc=1  pending_cmd=1 pending_n=2     # rect
733  dispatch pipe=2 rc=1  pending_cmd=1 pending_n=2     # rect
734  dispatch pipe=2 rc=1  pending_cmd=1 pending_n=2     # rect
736  flush rc=1  dirty=true                              # font route's entry flush
737  font-snapshot fb=1 bytes=12288 want=12288 quads=2
738  font-done status=promoted reason=fence-device-identity-readback-proven parity=true promotion_ready=true dispatched=2/2
739  flush    rc=-1 dirty=true cpu_fallback=false completion_unknown=false
740  dispatch pipe=2 rc=-1 pending_cmd=0 pending_n=0     # box  -> LOST
741  flush    rc=-1
742  dispatch pipe=2 rc=-1 pending_cmd=0 pending_n=0     # box  -> LOST
743  flush    rc=-1
744  dispatch pipe=2 rc=-1 pending_cmd=0 pending_n=0     # box  -> LOST
745  flush    rc=-1
746  flush    rc=-1
747  flush    rc=-1
748  readback-entry dirty=true pending_cmd=1 pending_n=2 cpu_fallback=false completion_unknown=false fb=1
749  flush    rc=-1
```

`vk_body=2304 vk_h1=742 vk_blue=0 vk_green=0 vk_amber=0`.

### What this says

1. **No restore fires.** The font composite promotes. (A) is dead.
2. **The lane dies immediately after the font composite.** Every single
   `_flush_pending_compute()` from line 739 onward returns **-1**, and every
   post-font primitive dispatch returns **rc=-1**. The three box rects are
   never recorded on the device. That, not a roll-back, is why they come back
   as body background.
3. **The Engine2D's backend still believes the pre-font command buffer is
   pending.** `-1` out of `_flush_pending_compute_impl` requires `cmd > 0` and
   then a failed `end_compute`/`submit`/`wait_idle`. But the font route's own
   entry flush at `backend_vulkan_font.spl:269` already submitted and cleared
   that batch (line 736, `rc=1`). So the object being flushed at 739 still
   carries `pending_compute_command = 1` — the clearing done inside
   `composite_font_batch` did not reach it. Every later operation then tries to
   end and submit a command buffer that was already consumed, fails, quarantines
   its descriptors, and returns -1.
4. **The state divergence is directly visible at readback.** Line 747 is a flush
   returning -1, whose `-1` path runs
   `_quarantine_pending_compute_descriptors()` + `_clear_pending_compute_state()`
   and therefore leaves `pending_compute_command = 0, pending_compute_count = 0`.
   Line 748 — the very next statement, `read_pixels_with_source()` on the same
   local binding (`engine.spl:2716-2721`) — reports **`pending_cmd=1
   pending_n=2`**. Those two lines cannot both describe one object. The backend
   the readback sees is a *different value* from the one the flushes mutated.
5. **That is also why the frame is silent.** `_dispatch_framebuffer_checked`
   does run its failure bookkeeping on `rc < 0` —
   `mark_cpu_fallback("framebuffer-dispatch-failed")` and
   `self.completion_unknown = true` — but line 748 shows the readback observing
   `cpu_fallback=false completion_unknown=false`. The flags are set on the same
   non-propagating value. So `read_pixels_with_source()` takes the healthy
   branch and returns `device_readback` with a positive handle, a real device
   identity, a full pixel count and `render_degraded=false`, for a frame that is
   missing every primitive issued after the text.

So the defect is **not** in the font route's roll-back logic and **not** in the
poison latch. It is: *a promoted `composite_font_batch` leaves the Engine2D's
`VulkanBackend` value holding stale `pending_compute_*` state, which breaks every
subsequent submission, and the resulting failure flags do not survive back to the
readback that publishes the frame.*

### Same-process discriminator

`engine_vecfont_probe.spl` (scratchpad) drives `Engine2D` directly — no HTML
lane — with the same bundled vector face the browser resolves
(`select_font_identity("sha256=a3041811...;axes=wght=100")`, `font_ready=true`),
in two orders:

```
software_boxfirst  body=1647 h1=760 blue=207 green=216 amber=216   cpu_mirror
vulkan_boxfirst    body=1647 h1=760 blue=207 green=216 amber=216   device_readback
```

Boxes issued **before** the text are bit-identical to software: they were
dispatched while the lane was still healthy. Its trace shows the identical
post-font collapse — `font-done status=promoted`, then `flush rc=-1`,
`flush rc=-1`, then `readback-entry ... pending_cmd=1 pending_n=2
cpu_fallback=false completion_unknown=false` — the lane is already dead, there
is simply nothing left to draw. The damage is also **not confined to the
engine that caused it**: the next arm's first two dispatches on a *freshly
created* `Engine2D` come back `rc=0` and flip `cpu_fallback=true`, because
`_enqueue_framebuffer_compute`'s `vulkan_sffi_reap_dependency_quarantine()`
gate is still refusing after the previous arm's quarantined descriptors.

A control that never enters the font composite stays clean:
`engine_order_probe.spl` uses `draw_text` with the bitmap default face, whose
plan rejects every non-`cpu` target, so `composite_font_batch` is never called
(no `font-*` lines at all) and the glyphs go through the CPU suffix's
`draw_image_blend` (`image-composite x=1 y=9 w=10 h=7 mode=1 rc=1`). Boxes drawn
after that text survive:

```
software_text body=1650 h1=756 blue=216 green=216 amber=216   cpu_mirror
vulkan_text   body=1650 h1=756 blue=216 green=216 amber=216   device_readback
```

This is the clean discrimination: **text alone does not break the lane — a
`composite_font_batch` call does**, whether it succeeds or not.

### Correction to an earlier draft of this section

An earlier version of this section argued (A) was refuted because "all the box
rects are dispatched BEFORE the text". That was an inference from a partial
trace — at the time the run had only reached line 736 — and it is **wrong**:
the completed trace shows four rects before the text and **three after**, and
the three that follow are exactly the ones that are lost. The refutation of (A)
does not depend on it; the measured `font-done status=promoted` with zero
`font-restore` lines is what refutes (A), and it is stronger. Recorded here
rather than quietly deleted so the next reader does not rediscover the wrong
argument from the git history.

### Fix direction

Standing policy is GPU-first with an honest fallback, so there are two separate
things to fix and they must not be conflated:

1. **Stop losing the primitives (the real fix).** After
   `composite_font_batch` returns, the Engine2D's `VulkanBackend` must observe
   the pending-batch state the font route actually left behind. The font route
   flushes at `backend_vulkan_font.spl:269` and clears
   `pending_compute_command`/`pending_compute_count`; that clearing has to reach
   the value stored back into `self.vulkan_backend` at `engine.spl:1466`.
   Re-flushing a consumed command-buffer handle is what produces the -1 cascade.
2. **Never publish a partial frame as device-proven (the honesty backstop).**
   `_dispatch_framebuffer_checked` already sets
   `mark_cpu_fallback("framebuffer-dispatch-failed")` and `completion_unknown`
   on `rc < 0`; the bug is that neither reaches `read_pixels_with_source()`.
   Until (1) lands, a readback taken from a backend whose pending state
   contradicts the last flush must fail closed to `cpu_fallback` +
   `render_degraded=true`. `pending_cmd`/`pending_n` disagreeing with the last
   flush result is a cheap, sufficient detector — it is exactly what lines
   747/748 show.

Do **not** attempt (2) alone. An honest degraded frame is better than a lying
one, but the lane is losing real GPU work and (1) is the actual defect.

### Perf defect found on the way (separate, filed here so it is not lost)

Between the entry flush (`backend_vulkan_font.spl:269`) and the framebuffer
snapshot (`:376`) the vulkan font route spent **over an hour of wall time and
~25 minutes of CPU** for a **two-glyph** draw at 64x48 under
`SIMPLE_EXECUTION_MODE=interpreter`. Both instrumented probes stalled there
identically with the process demonstrably busy (rising `utime`), so it is
compute, not a hang. The only whole-atlas work in that window is
`_vulkan_font_pixels_to_bytes(batch.atlas_pixels)` followed by
`sha256_u8_hex(atlas_payload)` at `:350-359` — an interpreted SHA-256 over the
entire glyph atlas on every batch that misses the
`font_atlas_generation`/`owner_identity` cache. This is what makes the bug
expensive to investigate and should be fixed independently (hash once per
face+generation, or move the digest to a native helper).

### Probe artifacts (scratchpad, this session)

- `vkorder/drop_trace.log` — the failing 64x48 browser-lane run with
  `[vk-order]` armed; source of the trace above
- `vkorder/engine_vecfont_probe.spl` / `vecfont.log` — direct `Engine2D` with
  the real bundled vector face, both draw orders; reproduces the post-font
  collapse without the HTML lane
- `vkorder/engine_order_probe.spl` / `engine_order.log`,
  `engine_order_v2.log` — bitmap-face control; `composite_font_batch` never
  called, vulkan == software bit-identical

## Fix (2026-08-04, second attempt) — the write-back. FIXED.

The second correction's mechanism (1) is correct and the defect is now closed.
The state `composite_font_batch` left behind never reached the Engine2D's
backend because of **one wrong binding form**, not because of anything the font
route does.

### The write-back site

`src/lib/gc_async_mut/gpu/engine2d/engine.spl`, the `elif target == "vulkan":`
arm of `_draw_font_batch_planned`'s `for target in plan:` loop. Before:

```
val active = self.vulkan_backend        # active : VulkanBackend?
if active == nil:
    attempts.push("vulkan:unavailable")
else:
    val vulkan = active                 # STILL VulkanBackend? -- the defect
    var evidence = vulkan.composite_font_batch(x, y, batch)
    self.last_vulkan_font_evidence = evidence
    self.vulkan_backend = Some(vulkan)  # re-wraps the UNMUTATED value
```

### Why the mutation was lost

`vulkan` here has static type `VulkanBackend?`. A `me` (mutating) method called
through an **option-typed** binding mutates a temporary unwrap that is then
discarded; the binding keeps its pre-call value, so `Some(vulkan)` stored the
backend exactly as it was before the font route ran. Every other vulkan route in
the file uses `if val Some(vulkan) = ...`, which **does** write back — which is
why the pre-text rects accumulated their pending state correctly and only the
font route lost it.

Minimal reproducer, `SIMPLE_EXECUTION_MODE=interpreter bin/simple run`
(`optwb_probe.spl`, scratchpad) — a class with `me bump()` held in a `Counter?`,
bumped twice through each binding form:

```
A n=0     # val ca = <optional>;         ca.bump(); ca.bump()   -- BOTH LOST
B n=2     # if val Some(cb) = opt:       cb.bump(); cb.bump()   -- correct
C n=2     # same as B through a nested `me` call                -- correct
```

Filed as its own language defect:
`me_method_mutation_through_optional_binding_discarded_2026-08-04.md`, which
also tables the 10+ remaining occurrences of the losing idiom.

That single lost write-back explains the entire trace: the font route's entry
flush (`backend_vulkan_font.spl:269`) consumed and cleared the pending compute
batch on the discarded copy, so the stored backend still held
`pending_compute_command = 1, pending_compute_count = 2`. Every later flush
tried to `end_compute`/`submit` an already-consumed command buffer, returned
`-1`, quarantined its descriptors, and no-op'd its primitive — and the
`mark_cpu_fallback("framebuffer-dispatch-failed")` / `completion_unknown` that
`_dispatch_framebuffer_checked` correctly sets landed on the same doomed copies,
so the readback published `device_readback` for a truncated frame.

### The change

1. **The real fix.** The vulkan font arm now binds with
   `if val Some(vulkan) = self.vulkan_backend:` (`else:` keeps the
   `attempts.push("vulkan:unavailable")` arm). Two sibling sites in the same
   file with the identical losing idiom and a mutating call are fixed the same
   way: `install_vulkan_font_spirv` (`install_font_atlas_pipeline`) and
   `draw_vulkan_image_blend_checked` (`draw_image_blend_checked`).
   `engine.spl:498` uses the idiom but only reads, so it is left alone. The
   non-vulkan backends (cuda/metal/opencl/rocm, and `engine3d/engine.spl`) carry
   the same defect and are tabled in the language bug — deliberately NOT changed
   here, because none of them initialize on this host and an unverifiable edit to
   a GPU dispatch path is worse than a filed defect.

2. **Honesty backstop** (`read_pixels_with_source`, same file). EVERY return path
   of `_flush_pending_compute` clears the pending batch, so pending state that
   *survives* the flush proves the value the flush mutated is not the value about
   to be read back. That condition now calls
   `mark_cpu_fallback("pending-compute-state-contradicts-flush")`, so the
   readback reports `cpu_fallback` and `_simple_web_layout_execute_draw_ir_composition`'s
   `lane_demoted` latch raises `render_degraded`. This is exactly the
   `pending_cmd`/`pending_n`-disagrees-with-the-last-flush detector the second
   correction specified. It is inert on the fixed lane (measured
   `pending_cmd=0 pending_n=0` at every readback below) — it never fires and so
   masks nothing; it exists so a future regression of this shape fails CLOSED
   instead of publishing a lying frame.

### Verification

All runs `SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_VK_ORDER_TRACE=1
SIMPLE_EXECUTION_MODE=interpreter bin/simple run`, each **bracketed** by a source
grep immediately before and after (`PRECHECK=7/1 POSTCHECK=7/1`, counting the
`if val Some(vulkan) = self.vulkan_backend:` gate sites and the backstop
string), so each result provably describes the fixed tree.

**Provenance.** Measured in the shared working copy at HEAD `9dcd16644b8`,
which is **64 commits behind** origin `3daf11f4ae9`. Origin tip does not
currently compile (`mir_to_llvm_translate_call_trait_break_2026-08-04.md`), so
these numbers are NOT a verification against origin tip. The change is confined
to `.spl` engine2d libraries and is independent of that compiler break.

**1. Browser lane with text, 64x48 same-run A/B** (`vulkan_drop_probe.spl`) —
the failing case. This is the fix:

| | software | vulkan BEFORE | vulkan AFTER |
|---|---|---|---|
| len | 3072 | 3072 | 3072 |
| body | 1656 | **2304** | **1656** |
| h1 | 742 | 742 | 742 |
| blue | 216 | **0** | **216** |
| green | 216 | **0** | **216** |
| amber | 216 | **0** | **216** |

**2. `[vk-order]` trace, same run — no `rc=-1` anywhere.** The post-font
dispatches now land on a FRESH command buffer (`pending_cmd=4`), which is the
direct receipt that the font route's flush reached the stored backend:

```
flush rc=1   dirty=true                              # font route's entry flush
font-snapshot fb=1 bytes=12288 want=12288 quads=2
font-done status=promoted parity=true dispatched=2/2
dispatch pipe=2 rc=1 pending_cmd=4 pending_n=1       # box -> LANDS  (was rc=-1)
dispatch pipe=2 rc=1 pending_cmd=4 pending_n=1       # box -> LANDS  (was rc=-1)
dispatch pipe=2 rc=1 pending_cmd=4 pending_n=1       # box -> LANDS  (was rc=-1)
flush rc=1
readback-entry dirty=false pending_cmd=0 pending_n=0 cpu_fallback=false completion_unknown=false
```

Compare the pre-fix trace in the second correction: `flush rc=-1` from line 739
onward, all three boxes `rc=-1`, and `readback-entry ... pending_cmd=1
pending_n=2`. The backstop's contradiction condition is false here (0/0 after a
successful flush), so it correctly does not fire.

**3. Direct-Engine2D vector-face probe** (`engine_vecfont_probe.spl`), which
reproduced the collapse without the HTML lane:

| arm | BEFORE | AFTER |
|-----|--------|-------|
| software_boxfirst | cpu_mirror 1647/760/207/216/216 | unchanged |
| vulkan_boxfirst | device_readback 1647/760/207/216/216 | **unchanged (control holds)** |
| software_textfirst | cpu_mirror 1647/760/216/216/216 | unchanged |
| vulkan_textfirst | **cpu_fallback 0/0/0/0/0** | **device_readback 1647/760/216/216/216 == software** |

The text-first vulkan arm went from a completely dead frame to bit-identical
with software.

**4. Bitmap-face control** (`engine_order_probe.spl`, never calls
`composite_font_batch`) — must not move, and does not. Diff against the
pre-fix `engine_order_v2.log` is EMPTY across all four arms:
`notext` and `text`, software and vulkan, all `216/216/216`,
vulkan `device_readback`.

**5. Quarantine leak — CLEARED as a consequence.** The second correction noted
that a *freshly created* `Engine2D` in the next arm had its first two dispatches
come back `rc=0` with `cpu_fallback=true`, because
`_enqueue_framebuffer_compute`'s `vulkan_sffi_reap_dependency_quarantine()` gate
was still refusing after the previous arm's quarantined descriptors. With the
write-back fixed there is no `-1` cascade, so
`_quarantine_pending_compute_descriptors()` is never reached and nothing is left
in quarantine. Measured on the second arm of the fixed `vecfont` run: the fresh
engine's first dispatches are `rc=1 pending_cmd=1 pending_n=1` with
`cpu_fallback=false`, and that arm reads back `device_readback`. The leak was a
downstream symptom of this defect, not a separate one.

### Still owed / still open

- **The regression spec** `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl`
  was again not run to a `Results:` line. Its lane resolves to `"software"`, so
  the expected impact is nil — but that remains an argument, not a measurement,
  and it is inherited from the previous fix attempt.
- **The perf defect is untouched.** The interpreted whole-atlas SHA-256 at
  `backend_vulkan_font.spl:350-359` still costs ~23 minutes of CPU per two-glyph
  draw; both verification runs above spent essentially all their wall time
  there. Fix independently (hash once per face+generation, or a native digest).
- **The sibling occurrences** of the option-binding write-back defect in
  `engine2d/engine.spl` (cuda/metal/opencl/rocm) and `engine3d/engine.spl` are
  filed and unfixed — see the language bug doc's table.
