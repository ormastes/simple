# Simple Host/GPU `later(...) gpu \:` — Architecture and Grammar

**Status:** Research / design proposal
**Domain:** language (grammar + lowering) × ui/runtime (host/GPU lane dispatch)
**Date:** 2026-06-14

> **Default grammar decision:** the lane marker is placed **after** `later(...)`
> and **before** the lambda, keeping `\:` / `\e:` as the real lambda grammar:
>
> ```
> target.later(options...) gpu \:
>     ...
> target.later(options...) host \:
>     ...
> ```

**Repo anchor:** Simple already parses backslash lambdas including `\x: expr`,
`\x, y: expr`, and `\: expr`; it also supports block-style lambda bodies after
the colon. This proposal builds the host/GPU lane system on that existing lambda
grammar.

---

## 1. Default syntax

The canonical delayed lambda syntax is:

```
target.later() host \:
    ...

target.later() gpu \:
    ...
```

With a parameter:

```
target.later() host \e:
    ...

target.later() gpu \e:
    ...
```

With packet/queue options:

```
target.later(
    lane: "control",
    max_packet: 512,
    max_capture: 128,
    max_ref_bytes: 0
) gpu \:
    ...
```

This replaces the earlier `target.host.later() \:` / `target.gpu.later() \:` as
the preferred public grammar. The old form may remain as sugar:

```
target.gpu.later() \:
    ...
```

but canonical style is:

```
target.later() gpu \:
    ...
```

## 2. Meaning

```
target.later(...) host \:
    body
```

means: run `body` on the host lane. If the caller is already host → direct call.
If the caller is GPU → send a GPU→Host queue packet.

```
target.later(...) gpu \:
    body
```

means: run `body` on the GPU lane. If the caller is already GPU → direct call.
If the caller is host → send a Host→GPU queue packet.

Compiler lowering:

```
same lane  -> direct call
other lane -> queue packet
```

## 3. Event handler grammar

The event handler itself can be lane-wrapped:

```
canvas.on_pointer_down(gpu \e:
    val hit = hit_buffer.lookup(e.x, e.y)

    host.later \:
        if hit.scene_key == scene.key:
            session.focus(hit.target_id)
)
```

Recommended normalized form:

```
canvas.on_pointer_down(gpu \e:
    val hit = hit_buffer.lookup(e.x, e.y)

    session.later(
        lane: "control",
        max_packet: 512,
        max_capture: 128
    ) host \:
        if hit.scene_key == scene.key:
            session.focus(hit.target_id)
)
```

Short form is allowed:

```
host.later \:
    ...
```

but internally lowers to a host target handle:

```
host_runtime.later(...) host \:
    ...
```

## 4. Mixed host/GPU event

For common UI events, use one event with host and GPU sections:

```
button.on_click \e:
    button.later(
        lane: "control",
        max_packet: 512,
        max_capture: 128
    ) host \:
        button.checked = not button.checked
        button.text = if button.checked: "ON" else: "OFF"

    button.later(
        lane: "control",
        max_packet: 256,
        max_capture: 64
    ) gpu \:
        button.opacity_milli = 1000
        button.scale_milli = 1050
        button.animate("scale_milli", 1050, 1000, 90)
```

- host part = semantic truth
- gpu part = render/effect acceleration

## 5. Short block sugar

For readability, this sugar may be supported:

```
button.on_click \e:
    host:
        button.checked = not button.checked
        button.text = if button.checked: "ON" else: "OFF"

    gpu:
        button.opacity_milli = 1000
        button.scale_milli = 1050
```

Compiler expands it to:

```
button.later(...) host \:
    ...

button.later(...) gpu \:
    ...
```

## 6. Full architecture

```
Host UI/Event Thread
  - native input
  - UISession
  - semantic event dispatch
  - host value update
  - layout truth
  - dirty-region truth
        |
        | target.later(...) gpu \:
        v
Host->GPU Queue Layer
  - control queue
  - frame queue
  - resource queue
  - packet-size validation
  - shared/gpu/staging references
        |
        v
GPU Submit Thread / GPU Worker
  - batch queue packets
  - reuse descriptors/resources
  - record command buffers
  - submit coarse-grained GPU work
        |
        v
GPU Device
  - render lambdas
  - animation/effects
  - hit-test assist
  - Draw IR / DisplayGraphIR execution
  - compute-heavy kernels
        |
        | target.later(...) host \:
        v
GPU->Host Queue Layer
  - host update proposals
  - tiny receipts
  - completion fence values
  - fault reports
        |
        v
Host Commit Thread
  - validate scene_key
  - validate revision
  - validate handle generation
  - run host continuation
  - mutate UISession
```

## 7. Core invariant

- Host owns semantic truth.
- GPU owns acceleration.
- GPU may propose host updates.
- Only the host commit lane mutates host semantic state.
- Remote calls pass handles and bounded payloads, never raw host references.

## 8. Lane types

### Host lane

Allowed: UISession mutation, widget value change, focus final decision,
accessibility update, text input / IME, file/network/security actions,
window close/process launch, semantic state commit.

```
button.later(max_packet: 512) host \:
    button.checked = true
    session.focus(button.id)
```

### GPU lane

Allowed: render-only state, opacity, transform, color, clip, animation phase,
hit-test assist, dirty tile compute, Draw IR batch execution,
image/glyph/rect compositing.

```
button.later(max_packet: 256) gpu \:
    button.opacity_milli = 920
    button.scale_milli = 1030
```

Forbidden:

```
button.later() gpu \:
    button.checked = true
```

Compiler diagnostic:

```
error: GPU lambda cannot mutate host semantic field `checked`.
Use target.later(...) host \: or return a host proposal.
```

## 9. Packet-size grammar

Packet-size options are written inside `later(...)`.

```
target.later(
    lane: "control",
    max_packet: 512,
    max_capture: 128,
    max_ref_bytes: 0
) gpu \:
    ...
```

Definitions:

| option | meaning |
|--------|---------|
| `lane` | queue class: `control`, `frame`, `resource`, `receipt` |
| `max_packet` | maximum queue packet bytes after lowering |
| `max_capture` | maximum copied lambda capture bytes |
| `max_ref_bytes` | maximum referenced shared/gpu/staging memory bytes |

```
chart.later(
    lane: "frame",
    max_packet: 512,
    max_capture: 128,
    max_ref_bytes: 16_MB
) gpu \:
    chart.draw_line(points_gpu)
```

## 10. Warning suppression rule

Do not support blind suppression (`no_warn: true`). Use checked size contracts:

```
target.later(max_packet: 4_KB) gpu \:
    ...
```

Compiler rule:

```
if estimated_packet <= max_packet:
    no warning
else:
    warning or error
```

If declared `max_packet: 512` but compiler estimates 2048 bytes:

```
error: lambda packet estimate 2048 bytes exceeds declared max_packet 512 bytes.
```

## 11. Large parameter strategy

**Small values** — small POD values are copied inline:

```
val color = 0xff33ccffu32

button.later(max_packet: 256) gpu \:
    button.color = color
```

**Large values** must become shared/gpu/staging refs.

Bad:

```
chart.later(max_packet: 512) gpu \:
    chart.draw(points)
```

Warning:

```
warning: GPU lambda captures `points` by copy: 800 KB.
max_packet is 512 bytes.
Use shared(points), gpu.copy(points), or staging(points).
```

Good shared-memory form:

```
val points_ref = shared(points)

chart.later(
    lane: "frame",
    max_packet: 512,
    max_capture: 128,
    max_ref_bytes: 8_MB
) gpu \:
    chart.draw(points_ref)
```

Good GPU-local form:

```
val points_gpu = gpu.copy(points)

chart.later(
    lane: "frame",
    max_packet: 512,
    max_capture: 128,
    max_ref_bytes: 16_MB
) gpu \:
    chart.draw(points_gpu)
```

Good staging upload form:

```
val image_stage = staging(image_pixels)

texture.later(
    lane: "resource",
    max_packet: 512,
    max_ref_bytes: 64_MB
) gpu \:
    texture.upload(image_stage)
```

## 12. Queue lanes

**Control lane** — tiny interactive work (hover, small render deltas, hit-test
proposal, focus proposal, cancel, fence):

```
button.later(
    lane: "control",
    max_packet: 256,
    max_capture: 64
) gpu \:
    button.opacity_milli = 920
```

**Frame lane** — coarse-grained per-frame work (Draw IR delta, dirty rect batch,
instance buffer ref, animation batch, composition batch):

```
scene.later(
    lane: "frame",
    max_packet: 4_KB,
    max_ref_bytes: 16_MB
) gpu \:
    scene.apply_draw_ir_delta(draw_ir_delta_ref)
```

**Resource lane** — uploads (image, glyph atlas, font atlas, large chart buffer,
path cache):

```
atlas.later(
    lane: "resource",
    max_packet: 512,
    max_ref_bytes: 32_MB
) gpu \:
    atlas.upload(glyph_stage)
```

**Receipt lane** — GPU→Host tiny results (completed seq, fence value, small
scalar result, host proposal, fault code). Do not use the receipt lane for full
framebuffer readback in the hot path.

## 13. Remote call packet

```
struct RemoteCall:
    seq: u64
    source_lane: Lane
    target_lane: Lane
    target_id: u64
    target_generation: u32
    method_id: u32
    type_id: u32
    payload_schema: u32
    scene_key: u64
    base_revision: u64
    payload_kind: PayloadKind
    inline_size: u32
    total_payload_size: u32
    payload_ref: PayloadRef
    flags: u32

enum PayloadKind:
    Inline
    SharedRef
    StagingRef
    GpuLocalRef
```

## 14. Host commit validation

Every GPU→Host update must pass validation:

```
fn commit_remote_call(call: RemoteCall):
    require call.target_generation == host_table.generation(call.target_id)
    require call.scene_key == session.scene_key
    require call.base_revision == session.revision
    require call.inline_size <= handle.max_payload_bytes
    dispatch_method(call.target_id, call.method_id, call.payload)
```

If stale: reject the stale proposal, do not mutate UISession, optionally request
replay/rebase.

## 15. GPU hit-test then host update

Canonical example:

```
canvas.on_pointer_down(gpu \e:
    val hit = hit_buffer.lookup(e.x, e.y)

    session.later(
        lane: "control",
        max_packet: 512,
        max_capture: 128
    ) host \:
        if hit.scene_key == scene.key:
            session.focus(hit.target_id)
            canvas.selected_id = hit.target_id
)
```

Meaning:

1. Event starts on GPU lane.
2. GPU reads the hit buffer.
3. GPU creates a host continuation packet.
4. Host commit thread validates scene_key/revision.
5. Host mutates session/focus/selection.

Short accepted form (lowers `host.later` to the host commit target):

```
canvas.on_pointer_down(gpu \e:
    val hit = hit_buffer.lookup(e.x, e.y)

    host.later \:
        if hit.scene_key == scene.key:
            session.focus(hit.target_id)
)
```

## 16. Type-level packet bounds

For reusable small packets:

```
@packet_bound(max: 64)
struct ButtonRenderDelta:
    opacity_milli: i32
    scale_milli: i32
    color: u32
```

Usage:

```
button.later(max_packet: 256) gpu \:
    button.update(ButtonRenderDelta(
        opacity_milli: 920,
        scale_milli: 1030,
        color: 0xff33ccffu32
    ))
```

## 17. Backend config

```
gpu_config desktop_vulkan:
    backend = "vulkan"
    process_isolation = true

    control.max_packet = 512
    frame.max_packet = 64_KB
    resource.max_packet = 1_MB

    handle_bytes = 32
    remote_call_header_bytes = 96
    alignment = 16

    supports_shared_host_visible = true
    supports_gpu_local = true
    supports_timeline_fence = true

    strict_packet_fit = false

gpu_config browser_webgpu:
    backend = "webgpu"
    process_isolation = true

    control.max_packet = 256
    frame.max_packet = 16_KB
    resource.max_packet = 256_KB

    handle_bytes = 40
    remote_call_header_bytes = 128
    alignment = 16

    supports_shared_host_visible = false
    supports_gpu_local = true

    strict_packet_fit = true
```

Compiler behavior:

```
packet fits selected backend:                       ok
packet fits selected backend but not fallback:      warning
strict_packet_fit and packet does not fit:          error
```

## 18. Warning algorithm

Estimate packet bytes:

```
packet_bytes =
    align(remote_call_header_bytes, alignment)
  + align(inline_capture_bytes, alignment)
  + handle_count * handle_bytes
  + method_payload_inline_bytes
  + debug/evidence_overhead
```

Track separately: inline packet bytes, copied capture bytes, referenced bytes,
queue worst-case bytes.

Severity:

```
error:      estimated_packet > declared max_packet
warning:    hot path packet exceeds backend lane soft limit
note:       cold path packet exceeds soft limit but is explicitly bounded
no warning: shared/gpu/staging ref is used and bounds fit
```

Hot paths: `pointer_move`, `hover`, `scroll`, `frame`, `animation`.
Cold paths: `startup`, `resource_load`, `debug`, `test`.

Group warnings:

```
warning: 42 GPU lambdas capture BigTheme by copy on control lane.
largest packet=12 KB, control.max_packet=512 B.
suggestion: use shared(BigTheme), gpu.copy(BigTheme), or make BigTheme packet_bound.
```

## 19. Coarse-grained GPU rule

Good:

```
scene.later(
    lane: "frame",
    max_packet: 4_KB,
    max_ref_bytes: 16_MB
) gpu \:
    scene.apply_draw_ir_delta(draw_ir_delta_ref)
```

Bad:

```
for button in buttons:
    button.later() gpu \:
        button.draw()
```

Compiler warning:

```
warning: per-widget GPU later() call inside loop.
Use frame-level Draw IR batch, instance buffer, or DisplayGraphIR delta.
```

GPU calls should be coarse-grained: one frame packet, one Draw IR delta, one
dirty tile batch, one resource upload batch, one animation batch, one hit-test
batch — not per widget.

## 20. Final canonical grammar

```
target.later() host \:
    ...

target.later() gpu \:
    ...

target.later(options...) host \x:
    ...

target.later(options...) gpu \x:
    ...

event_source.on_event(host \e:
    ...
)

event_source.on_event(gpu \e:
    ...
)
```

Accepted sugar:

```
host.later \:
    ...

gpu.later \:
    ...
```

Canonical explicit form:

```
target.later(
    lane: "control",
    max_packet: 512,
    max_capture: 128,
    max_ref_bytes: 0
) gpu \:
    ...
```

## 21. Final invariant

1. `\:` remains Simple's no-parameter lambda.
2. The lane marker goes **after** `later(...)`: `later(...) gpu \:`.
3. Event handlers may use `host \e:` or `gpu \e:`.
4. Same-lane `later` is a direct call.
5. Cross-lane `later` is a queue packet.
6. Packet-size contracts are checked.
7. Large data must use shared/gpu/staging refs.
8. GPU can propose host updates.
9. Only the host commit lane mutates host semantic state.
10. GPU work should be coarse-grained: frame/render/resource batches, not
    per-widget dispatch.

This makes the preferred form the default — `target.later(...) gpu \:` — and
keeps `host.later \:` usable inside GPU handlers for the
"GPU hit-test → host commit" pattern.
