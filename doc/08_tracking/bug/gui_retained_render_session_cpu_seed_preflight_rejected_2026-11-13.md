# `GuiRetainedRenderSession.seed` is rejected on the cpu backend: `fresh-device-command-preflight-required`

- Status: FIXED (2026-11-13, lane uia2) — see "Resolution" at the end
- Severity: P3
- Found by: lane uia while re-verifying
  `gui_content_renderer_parser_expected_pattern_found_use_2026-08-12` (that
  record's parse error does not reproduce; this does).
- Base: release/1.0.0 `35144b7f5e9`, Linux aarch64, Rust seed sha256 prefix
  `af717f53d6bce3e5`.

## Repro

```
simple test test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl
3 examples, 2 failures
```

- "reuses a seeded idle frame without rebuilding widget DrawIR":
  `retained.seed(session)` returns false (`expected false to equal true`), then
  `readback.source` is `preflight_rejected` instead of `not_requested` /
  `cpu_mirror`, pixel count 0 instead of 512.
- "seeds the first damaged-render call with one valid full-frame plan":
  `unsupported_kinds` is `retained-seed-failed` instead of `none`.

## What was measured

A probe calling the same executor the session uses, on
`build_tree(column("root", [label("message", "ready")]))`, 32x16, backend `cpu`:

```
engine2d_draw_ir_render_composition_damaged_with_images(engine, composition, [], [0,0,32,16], false)
-> unsupported=fresh-device-command-preflight-required ops=0 tiles=0 src=preflight_rejected
```

The reason string has one producer:
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:1326`
(`_engine2d_draw_ir_fresh_device_reason`), returned when
`_engine2d_draw_ir_fresh_device_command_supported` refuses a command of the
canonical widget composition.

## Not established

- Which command of the label composition is refused, and why (text command,
  style key, or font state).
- Which commit turned the spec red. Candidates by date only, not bisected:
  `92b33870986` (fast-lane text no-ink refusal), `c2521b32190`, `69166cadc70`.

## Acceptance

`gui_content_renderer_spec.spl` 3/3 on the cpu backend without weakening its
assertions.

## 2026-11-13 follow-up: the refused command is the label text

Dump of `session.submit_widget_draw_ir(32, 16, "cpu")` for the spec's tree:

```
batch=widget-main emb=0,0 32x16 op=1000 surf=widget-root
  cmd kind=rect at=0,0 32x16
  cmd kind=rect at=0,0 32x16
  cmd kind=text at=3,2 36x12 text=ready
```

The text command spans x=3..39 on a 32-wide target. The batch fills the target,
so `_engine2d_draw_ir_fresh_device_command_supported` is called with
`allow_clipped=false` and returns false for a text command that is not wholly
bounded (`draw_ir_adv.spl:1210`). That is the rejection.

Still not established: whether the 36px text box is new (a text-metric change
would make the spec's 32x16 fixture too small) or whether the fresh-device
preflight is meant to admit a clipped text command on a full-target batch. The
first is a fixture question, the second a product one; do not widen the
fixture or the preflight without deciding which.

## Resolution (2026-11-13, lane uia2, work/uia2-gui-content-20261113)

**Decision: neither the layout nor the spec oracle is wrong. The seed called the
wrong executor.**

- The 36px box is not metric drift. `_default_text` sizes a label from the
  pinned Noto Sans Mono face (12px, 7.2px advance, 5 glyphs), and the lowerer's
  `x + 2` offset is unchanged since the spec was written. The label overhung
  the 32px fixture on the day the spec landed (`9dc4e88f661`, 2026-08-12) and
  the spec was green, because `seed` then used the ordered composition executor
  (`engine2d_draw_ir_adv_composition_with_images`), which paints overhanging
  text clipped to the target — the same call the one-shot
  `gui_session_content_frame` in the same file still makes.
- `d86b7ef59e2` (2026-08-13, "retain authoritative cpu engine state") switched
  `seed` to `engine2d_draw_ir_render_composition_damaged_with_images` to keep
  the mutated `Engine2D`. That wrapper applies the fresh-device preflight, hence
  the rejection reported above.
- Relaxing the preflight alone does not help; measured. With overhanging text
  admitted on a damage-clipped full-target batch, the tiled executor rejects the
  same composition with `retained-composition-unsafe-embedding`: the default
  theme's root surface requests window-surface glass and so samples its parent
  (`_engine2d_draw_ir_batch_samples_parent`). The tiled executor is by design
  not the owner of such a list. The preflight is left untouched.
- Fix: `GuiRetainedRenderSession.seed` now calls
  `engine2d_draw_ir_adv_composition_owner_with_images`, the ordered executor in
  its owner form, which returns the mutated engine `d86b7ef59e2` wanted, and
  accepts the frame on the one-shot path's criteria (no fallback, skipped ==
  occluded, full pixel count) plus `rendered_command_count > 0`.

Evidence (seed-fix Rust seed, Linux aarch64, base `d66bc5eaf82`):

- red `f06707aaef0`: `gui_content_renderer_spec.spl` 5 examples, 3 failures.
- green: 5 examples, 0 failures. The original three examples are unmodified.
  New example 4 pins the retained seed readback byte-equal to the one-shot
  frame for the overhanging label; example 5 pins that
  `engine2d_draw_ir_adv_fresh_device_composition_with_images` still rejects
  the same composition with `fresh-device-command-preflight-required`.

### Still open, not fixed here

A NON-idle damage plan on this session is still rejected. Probe after the fix:
`seed=true`, plan `mode=1 rects=4` (one 8x8 dirty tile), then
`render_damage -> unsupported=retained-composition-unsafe-embedding ops=0
src=preflight_rejected`. `render_damage` hands a parent-sampling root to the
single-root tiled fast path instead of routing it through the ordered executor.
`GuiRetainedRenderSession` has no caller outside its spec today, so nothing
ships broken, but the class cannot replay damage under the default theme.
