# simple_2d_web_renderer_gpu_optimization_spec

> This executable contract proves the backend-neutral lifecycle required before Simple 2D or Simple Web may claim GPU-resident asynchronous presentation. It is for renderer implementers, performance reviewers, and release verifiers.

<!-- sdn-diagram:id=simple_2d_web_renderer_gpu_optimization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_2d_web_renderer_gpu_optimization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_2d_web_renderer_gpu_optimization_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_2d_web_renderer_gpu_optimization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_2d_web_renderer_gpu_optimization_spec

This executable contract proves the backend-neutral lifecycle required before Simple 2D or Simple Web may claim GPU-resident asynchronous presentation. It is for renderer implementers, performance reviewers, and release verifiers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_2d_web_renderer_gpu_optimization.md |
| Plan | doc/03_plan/sys_test/simple_2d_web_renderer_gpu_optimization.md |
| Design | doc/05_design/simple_2d_web_renderer_gpu_optimization.md |
| Research | doc/01_research/local/simple_2d_web_renderer_gpu_optimization.md |
| Source | `test/03_system/app/ui.browser/feature/simple_2d_web_renderer_gpu_optimization_spec.spl` |
| Updated | 2026-09-10 |
| Generator | `simple spipe-docgen` (Simple); manual mirror refreshed while the admitted worker is unavailable |

## Overview

This executable contract proves the backend-neutral lifecycle required before
Simple 2D or Simple Web may claim GPU-resident asynchronous presentation. It is
for renderer implementers, performance reviewers, and release verifiers.

The scenario deliberately distinguishes a GPU submission from a CPU queue
operation. A frame is presented only after a named device submission and its
matching fence complete. Normal presentation reports zero readback bytes.

## Assumptions and scope

The test exercises the shared retained-surface owner, frame ring, submission
identity, and event-damage freeze boundary. It does not claim that a physical
Vulkan, Metal, or DirectX device ran; native backend receipts and benchmark
evidence are separate acceptance gates in the linked test plan.

The retained ring contains two or three slots. Surface resize and shutdown are
legal only after all submitted work retires. Event normalization remains owned
by `gpu_web_event_model`; this contract consumes its normalized batch.

## Primary workflow

1. Create one retained 4K render surface and its bounded frame ring.
2. Accumulate generation-checked event damage and clip it to the viewport.
3. Freeze the pending damage and upload byte count into one recording slot.
4. Submit the slot with a backend and device identity plus fence value.
5. Complete only the exact matching device token.
6. Present with zero CPU readback and release the slot for reuse.

## Syntax and examples

`gpu_event_damage_accumulate` accepts pending damage only for the current scene
generation. `gpu_event_damage_freeze` transfers that damage to a frame slot and
returns a fresh pending accumulator, preventing later input from mutating an
in-flight frame. `gpu_render_surface_complete` rejects mismatched fences.

The backpressure scenario fills every slot and expects `frame-ring-full` from
the next begin request. It never completes work inline merely to make space.

## Verification and evidence

The twelve scenarios provide happy, edge, and rejection paths for each covered
requirement. Assertions inspect frame state, token admission, damage bounds,
upload bytes, memory release, and readback bytes. Passing this spec proves the
portable lifecycle contract; it is not a substitute for physical-device traces
or the C Vulkan and Chrome differential receipts.

The companion [comparison-admission manual](../../../check/perf_comparison_admission_contract_spec.md)
owns equal fixture, viewport, timing, readback/capture, GPU identity, warmup,
sample, and checksum metadata for C Vulkan/Simple and Chrome/Simple rows. It
fails closed for software, unknown, synthetic, unverified, and fallback
identities. The typed host-frame acknowledgement and Vulkan context-admission
unit contracts separately specify that pending/unknown event work cannot advance
input, dirty regions and external-frame revisions remain owned until exact
acknowledgement, and `async_claim=false` remains in force until provider
authority exists. Retained GPU buffers and leases stay bound to their
surface/device generation; a positive local or recycled handle is not
submission authority.

## Scenario catalogue

### Device presentation

- The success case records damage, submits a Vulkan-identified token, matches
  its fence, and asserts that presentation transfers zero bytes to the CPU.
- The early-present case keeps the slot in recording state and requires a
  `slot-not-device-complete` refusal.
- The provenance case labels a token as software and requires fail-closed
  rejection before submission.

### Retained allocation lifecycle

- The create case asserts that a three-slot request creates exactly three
  retained frame slots rather than allocating per drawing operation.
- The busy-resize case proves that resource generations cannot be replaced
  while recorded work still owns the old surface.
- The shutdown case proves that retained and staging byte counters both reach
  zero when an idle surface is destroyed.

### Asynchronous frame ring

- The concurrency case submits three independently identified frames without
  completing any of them in the submission scope.
- The saturation case proves the producer receives backpressure when every
  slot is busy; the implementation cannot disguise synchronous draining as
  asynchronous work.
- The mismatch case proves that an unrelated fence cannot retire or recycle a
  submitted slot.

### Event and damage workflow

- The damage case clips rectangles to the viewport and coalesces only pending
  work before it is assigned to a frame generation.
- The stale-scene case rejects obsolete input without changing pending state.
- The freeze case asserts that the submitted slot retains its event generation
  while a fresh accumulator is returned for later events.

## Release interpretation

A green result admits the common lifecycle implementation for integration. It
does not admit a release by itself. Release evidence additionally requires a
real backend token, a device fence or timeline value, physical or headless GPU
execution as declared by the target profile, and separate display/capture
receipts. The comparison harness must use identical pixels, dimensions, event
scripts, warm-up policy, and sample boundaries for C Vulkan, Simple Vulkan,
Simple Web, and Chrome.

Normal presentation must never perform checksum, fingerprint, screenshot, or
full-frame readback work. Those operations belong to an explicit diagnostic or
capture request and must report their transferred byte count. A capture also
needs an exact token/generation, device-origin source, dimensions, stride,
byte count, and checksum. A CPU cache or synthetic present is not device
evidence. A benchmark that includes capture on one side but not the other is
inadmissible.

## Limitations and troubleshooting

An `invalid-submission-token` result means backend, device identity, timestamp,
submission id, or fence provenance is missing. `frame-ring-full` is expected
backpressure while all slots remain submitted. `stale-scene-generation` means
the event was authored against an obsolete scene and must be discarded.

If this contract passes but a backend stalls, inspect the backend adapter's
real submission token and completion callback. If presentation performs a
readback, route it through the explicit capture path instead of weakening the
zero-readback presentation assertion.

No runtime result is claimed by this manual update: the clean PR worktree has
no admitted pure-Simple worker, so docgen and compiled execution remain
pending. The source/manual pair is intentionally evidence-first.

**Requirements:** doc/02_requirements/feature/simple_2d_web_renderer_gpu_optimization.md

**NFR:** doc/02_requirements/nfr/simple_2d_web_renderer_gpu_optimization.md

**Research:** doc/01_research/local/simple_2d_web_renderer_gpu_optimization.md

**Plan:** doc/03_plan/sys_test/simple_2d_web_renderer_gpu_optimization.md

**Architecture:** doc/04_architecture/simple_2d_web_renderer_gpu_optimization.md

**Design:** doc/05_design/simple_2d_web_renderer_gpu_optimization.md

## Scenarios

### Simple 2D and Web renderer GPU optimization

### REQ-GPUUI-002: device presentation avoids CPU readback

#### should present a fence-complete frame with zero readback

- Record and submit one damaged frame
   - Expected: reason equals `presented`
   - Expected: receipt.readback_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record and submit one damaged frame")
val (recording, slot) = system_recording(1)
val (submitted, _) = gpu_render_surface_submit(
    recording, slot, system_token(1, 1))
val (complete, _) = gpu_render_surface_complete(
    submitted, slot, 1, 1001)
val (_, receipt, reason) = gpu_render_surface_present(complete, slot)
expect(reason).to_equal("presented")
expect(receipt.readback_bytes).to_equal(0)
```

</details>

#### should refuse presentation before device completion

- Attempt to present a recording frame
   - Expected: reason equals `slot-not-device-complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt to present a recording frame")
val (recording, slot) = system_recording(1)
val (_, _, reason) = gpu_render_surface_present(recording, slot)
expect(reason).to_equal("slot-not-device-complete")
```

</details>

#### should reject a software submission identity

- Submit a token without GPU provenance
   - Expected: reason equals `invalid-submission-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a token without GPU provenance")
val (recording, slot) = system_recording(1)
var token = system_token(1, 1)
token.backend = "software"
val (_, reason) = gpu_render_surface_submit(recording, slot, token)
expect(reason).to_equal("invalid-submission-token")
```

</details>

### REQ-GPUUI-003: retained buffers have explicit lifecycle

#### should allocate only the bounded frame ring

- Create a retained 4K surface
   - Expected: state.allocation_count equals `3`
   - Expected: state.slots.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a retained 4K surface")
val state = gpu_render_surface_create(41, 3840, 2160, 3,
    33554432, 1048576)
expect(state.allocation_count).to_equal(3)
expect(state.slots.len()).to_equal(3)
```

</details>

#### should reject resize while a frame is in flight

- Record damage before resizing
   - Expected: reason equals `frames-still-in-flight`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record damage before resizing")
val (recording, _) = system_recording(1)
val (_, reason) = gpu_render_surface_resize(
    recording, 1920, 1080, 16777216, 524288)
expect(reason).to_equal("frames-still-in-flight")
```

</details>

#### should release retained and staging bytes on shutdown

- Shut down an idle retained surface
   - Expected: reason equals `shutdown`
   - Expected: stopped.retained_bytes equals `0`
   - Expected: stopped.staging_bytes equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Shut down an idle retained surface")
val state = gpu_render_surface_create(41, 3840, 2160, 2,
    33554432, 1048576)
val (stopped, reason) = gpu_render_surface_shutdown(state)
expect(reason).to_equal("shutdown")
expect(stopped.retained_bytes).to_equal(0)
expect(stopped.staging_bytes).to_equal(0)
```

</details>

### REQ-GPUUI-004: submissions use a bounded asynchronous ring

#### should keep three independently identified frames in flight

- Fill every frame-ring slot without completing on the CPU
   - Expected: reason equals `submitted`
   - Expected: state.slots.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill every frame-ring slot without completing on the CPU")
var state = gpu_render_surface_create(41, 100, 100, 3, 40000, 4096)
var generation: i64 = 1
while generation <= 3:
    val (recording, slot, _) = gpu_render_surface_begin(
        state, generation, 10, 40)
    val (submitted, reason) = gpu_render_surface_submit(
        recording, slot, system_token(1, generation))
    expect(reason).to_equal("submitted")
    state = submitted
    generation = generation + 1
expect(state.slots.len()).to_equal(3)
```

</details>

#### should apply backpressure instead of draining immediately

- Request a fourth frame while all slots are submitted
   - Expected: slot equals `-1`
   - Expected: reason equals `frame-ring-full`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request a fourth frame while all slots are submitted")
var state = gpu_render_surface_create(41, 100, 100, 2, 40000, 4096)
var generation: i64 = 1
while generation <= 2:
    val (recording, slot, _) = gpu_render_surface_begin(
        state, generation, 10, 40)
    val (submitted, _) = gpu_render_surface_submit(
        recording, slot, system_token(1, generation))
    state = submitted
    generation = generation + 1
val (_, slot, reason) = gpu_render_surface_begin(state, 3, 10, 40)
expect(slot).to_equal(-1)
expect(reason).to_equal("frame-ring-full")
```

</details>

#### should retire only a matching device fence

- Report the wrong fence for a submitted frame
   - Expected: reason equals `completion-token-mismatch`
   - Expected: unchanged.slots[slot].state equals `GPU_FRAME_SUBMITTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report the wrong fence for a submitted frame")
val (recording, slot) = system_recording(1)
val (submitted, _) = gpu_render_surface_submit(
    recording, slot, system_token(1, 1))
val (unchanged, reason) = gpu_render_surface_complete(
    submitted, slot, 1, 9999)
expect(reason).to_equal("completion-token-mismatch")
expect(unchanged.slots[slot].state).to_equal(GPU_FRAME_SUBMITTED)
```

</details>

### REQ-GPUUI-005: events produce generation-checked damage

#### should clip and coalesce damage before frame submission

- Accumulate two event damage rectangles
   - Expected: reason equals `accumulated`
   - Expected: two.left equals `0`
   - Expected: two.right equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accumulate two event damage rectangles")
val surface = gpu_render_surface_create(41, 100, 100, 2, 40000, 4096)
val initial = gpu_pending_event_damage_for_surface(surface.surface, 8u64)
val (one, _) = gpu_event_damage_accumulate(initial,
    system_batch(8u64), 1, [-10, 10, 30, 20], 100, 100)
val (two, reason) = gpu_event_damage_accumulate(one,
    system_batch(8u64), 2, [80, 80, 30, 30], 100, 100)
expect(reason).to_equal("accumulated")
expect(two.left).to_equal(0)
expect(two.right).to_equal(100)
```

</details>

#### should reject an event authored for a stale scene

- Accumulate damage from the previous scene generation
   - Expected: reason equals `stale-scene-generation`
   - Expected: unchanged.has_damage is `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accumulate damage from the previous scene generation")
val surface = gpu_render_surface_create(41, 100, 100, 2, 40000, 4096)
val pending = gpu_pending_event_damage_for_surface(surface.surface, 8u64)
val (unchanged, reason) = gpu_event_damage_accumulate(pending,
    system_batch(7u64), 1, [0, 0, 10, 10], 100, 100)
expect(reason).to_equal("stale-scene-generation")
expect(unchanged.has_damage).to_be(false)
```

</details>

#### should freeze submitted damage away from later events

- Freeze one event generation into a frame slot
   - Expected: reason equals `damage-frozen`
   - Expected: recording.slots[slot].event_generation equals `5`
   - Expected: next.event_generation equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Freeze one event generation into a frame slot")
val surface = gpu_render_surface_create(41, 100, 100, 2, 40000, 4096)
val (pending, _) = gpu_event_damage_accumulate(
    gpu_pending_event_damage_for_surface(surface.surface, 8u64), system_batch(8u64), 5,
    [10, 10, 20, 30], 100, 100)
val (recording, next, slot, reason) = gpu_event_damage_freeze(
    surface, pending, 4)
expect(reason).to_equal("damage-frozen")
expect(recording.slots[slot].event_generation).to_equal(5)
expect(next.event_generation).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/simple_2d_web_renderer_gpu_optimization.md](doc/02_requirements/feature/simple_2d_web_renderer_gpu_optimization.md)
- **Plan:** [doc/03_plan/sys_test/simple_2d_web_renderer_gpu_optimization.md](doc/03_plan/sys_test/simple_2d_web_renderer_gpu_optimization.md)
- **Design:** [doc/05_design/simple_2d_web_renderer_gpu_optimization.md](doc/05_design/simple_2d_web_renderer_gpu_optimization.md)
- **Research:** [doc/01_research/local/simple_2d_web_renderer_gpu_optimization.md](doc/01_research/local/simple_2d_web_renderer_gpu_optimization.md)


</details>
