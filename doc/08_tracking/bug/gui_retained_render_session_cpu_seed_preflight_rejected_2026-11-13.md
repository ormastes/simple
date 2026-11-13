# `GuiRetainedRenderSession.seed` is rejected on the cpu backend: `fresh-device-command-preflight-required`

- Status: OPEN (2026-11-13)
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
