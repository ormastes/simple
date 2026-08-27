# Engine2dWmFrameExecutor — Branch Coverage Closure

> Purpose: Prove that backend target and recompose helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2dWmFrameExecutor — Branch Coverage Closure

Purpose: Prove that backend target and recompose helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that backend target and recompose helpers.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### backend target and recompose helpers

#### selects host, cpu_simd and cpu targets by gate order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects host, cpu_simd and cpu targets by gate order
- Verify: selects host, cpu_simd and cpu targets by gate order
   - Expected: engine2d_wm_draw_ir_backend_target(true, "metal", false) equals `metal`
   - Expected: engine2d_wm_draw_ir_backend_target(true, "vulkan", true) equals `vulkan`
   - Expected: engine2d_wm_draw_ir_backend_target(true, "", true) equals `cpu_simd`
   - Expected: engine2d_wm_draw_ir_backend_target(false, "metal", true) equals `cpu_simd`
   - Expected: engine2d_wm_draw_ir_backend_target(false, "", false) equals `DRAW_IR_BACKEND_CPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("selects host, cpu_simd and cpu targets by gate order")
step("Verify: selects host, cpu_simd and cpu targets by gate order")
# @req: REQ-OS-COMPOSITOR-001
expect(engine2d_wm_draw_ir_backend_target(true, "metal", false)).to_equal("metal")
expect(engine2d_wm_draw_ir_backend_target(true, "vulkan", true)).to_equal("vulkan")
expect(engine2d_wm_draw_ir_backend_target(true, "", true)).to_equal("cpu_simd")
expect(engine2d_wm_draw_ir_backend_target(false, "metal", true)).to_equal("cpu_simd")
expect(engine2d_wm_draw_ir_backend_target(false, "", false)).to_equal(DRAW_IR_BACKEND_CPU)
```

</details>

#### requires local recompose only when targets differ

- requires local recompose only when targets differ
- Verify: requires local recompose only when targets differ


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires local recompose only when targets differ")
step("Verify: requires local recompose only when targets differ")
assert_true(engine2d_wm_draw_ir_local_recompose_required("vulkan", "cpu"))
assert_false(engine2d_wm_draw_ir_local_recompose_required("cpu", "cpu"))
```

</details>

#### clamps negative dims in the fail-closed full plan

- clamps negative dims in the fail-closed full plan
- Verify: clamps negative dims in the fail-closed full plan
   - Expected: clamped.planned_pixels equals `0`
   - Expected: clamped.mode equals `DAMAGE_PLAN_FULL`
   - Expected: normal.planned_pixels equals `35`
   - Expected: normal.fallback_reason equals `DAMAGE_FALLBACK_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps negative dims in the fail-closed full plan")
step("Verify: clamps negative dims in the fail-closed full plan")
val clamped = engine2d_wm_full_damage_plan(-3, -4)
expect(clamped.planned_pixels).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(clamped.mode).to_equal(DAMAGE_PLAN_FULL)
val normal = engine2d_wm_full_damage_plan(5, 7)
expect(normal.planned_pixels).to_equal(35)  # oracle: 35 — named expected value from the requirement
expect(normal.fallback_reason).to_equal(DAMAGE_FALLBACK_INVALID)
```

</details>

### create backend-target wiring

#### records cpu_simd as both targets when enabled

- records cpu_simd as both targets when enabled
- Verify: records cpu_simd as both targets when enabled
   - Expected: executor.draw_ir_backend_target equals `cpu_simd`
   - Expected: executor.local_draw_ir_backend_target equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("records cpu_simd as both targets when enabled")
step("Verify: records cpu_simd as both targets when enabled")
val executor = Engine2dWmFrameExecutor.create(
    Engine2D.create_with_backend(8, 8, "cpu"),
    FramebufferDriver.empty(), W, H, true)
expect(executor.draw_ir_backend_target).to_equal("cpu_simd")
expect(executor.local_draw_ir_backend_target).to_equal("cpu_simd")
```

</details>

#### defaults to the cpu draw target

- defaults to the cpu draw target
- Verify: defaults to the cpu draw target
   - Expected: executor.draw_ir_backend_target equals `DRAW_IR_BACKEND_CPU`
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defaults to the cpu draw target")
step("Verify: defaults to the cpu draw target")
val executor = _executor()
expect(executor.draw_ir_backend_target).to_equal(DRAW_IR_BACKEND_CPU)
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

### create_host_gpu early-exit lattice

#### falls back with no mapped base

- falls back with no mapped base
- Verify: falls back with no mapped base
   - Expected: executor.host_gpu_base equals `0u64`
   - Expected: executor.draw_ir_backend_target equals `DRAW_IR_BACKEND_CPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back with no mapped base")
step("Verify: falls back with no mapped base")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    0u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    W, H, boot_monotonic_now_us())
expect(executor.host_gpu_base).to_equal(0u64)
assert_false(executor.host_gpu_required)
expect(executor.draw_ir_backend_target).to_equal(DRAW_IR_BACKEND_CPU)
```

</details>

#### rejects with no mapped base when the backend is required

- rejects with no mapped base when the backend is required
- Verify: rejects with no mapped base when the backend is required
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects with no mapped base when the backend is required")
step("Verify: rejects with no mapped base when the backend is required")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    0u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    W, H, boot_monotonic_now_us(), false, true)
expect(executor.host_gpu_base).to_equal(0u64)
assert_true(executor.host_gpu_required)
```

</details>

#### falls back on zero scanout dims even with a mapped base

- falls back on zero scanout dims even with a mapped base
- Verify: falls back on zero scanout dims even with a mapped base
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back on zero scanout dims even with a mapped base")
step("Verify: falls back on zero scanout dims even with a mapped base")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    0, 0, boot_monotonic_now_us())
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

#### falls back when the readback capacity is exceeded

- falls back when the readback capacity is exceeded
- Verify: falls back when the readback capacity is exceeded
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back when the readback capacity is exceeded")
step("Verify: falls back when the readback capacity is exceeded")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    8, 99999999, boot_monotonic_now_us())
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

#### falls back on an unsupported guest isa

- falls back on an unsupported guest isa
- Verify: falls back on an unsupported guest isa
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back on an unsupported guest isa")
step("Verify: falls back on an unsupported guest isa")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, 99, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    W, H, boot_monotonic_now_us())
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

#### rejects an invalid backend code when required

- rejects an invalid backend code when required
- Verify: rejects an invalid backend code when required
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an invalid backend code when required")
step("Verify: rejects an invalid backend code when required")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, SIMPLEOS_HOST_GPU_ISA_X86_64, 0,
    W, H, boot_monotonic_now_us(), false, true)
expect(executor.host_gpu_base).to_equal(0u64)
assert_true(executor.host_gpu_required)
```

</details>

#### falls back on an invalid negotiation clock

- falls back on an invalid negotiation clock
- Verify: falls back on an invalid negotiation clock
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("falls back on an invalid negotiation clock")
step("Verify: falls back on an invalid negotiation clock")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    W, H, 0)
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

#### times out before any attempt when the start is in the future

- times out before any attempt when the start is in the future
- Verify: times out before any attempt when the start is in the future
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("times out before any attempt when the start is in the future")
step("Verify: times out before any attempt when the start is in the future")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    W, H, boot_monotonic_now_us() + 1000000000)
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

#### times out before any attempt when the budget already elapsed

- times out before any attempt when the budget already elapsed
- Verify: times out before any attempt when the budget already elapsed
   - Expected: executor.host_gpu_base equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("times out before any attempt when the budget already elapsed")
step("Verify: times out before any attempt when the budget already elapsed")
val executor = Engine2dWmFrameExecutor.create_host_gpu(
    Engine2D.create_with_backend(8, 8, "cpu"), FramebufferDriver.empty(),
    4096u64, SIMPLEOS_HOST_GPU_ISA_X86_64, SIMPLEOS_HOST_GPU_BACKEND_VULKAN,
    W, H, boot_monotonic_now_us() - 2 * SIMPLEOS_HOST_GPU_NEGOTIATION_BUDGET_US)
expect(executor.host_gpu_base).to_equal(0u64)
```

</details>

### render admission gates

#### rejects non-positive revisions

- rejects non-positive revisions
- Verify: rejects non-positive revisions
   - Expected: executor.render(_scene([]), _taskbar(), [], 0, 1, "09:41") equals `0`
   - Expected: executor.render(_scene([]), _taskbar(), [], 1, 0, "09:41") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects non-positive revisions")
step("Verify: rejects non-positive revisions")
var executor = _executor()
expect(executor.render(_scene([]), _taskbar(), [], 0, 1, "09:41")).to_equal(0)
expect(executor.render(_scene([]), _taskbar(), [], 1, 0, "09:41")).to_equal(0)
```

</details>

#### rejects when host gpu is required but never negotiated

- rejects when host gpu is required but never negotiated
- Verify: rejects when host gpu is required but never negotiated
   - Expected: executor.render(_scene([]), _taskbar(), [], 1, 1, "09:41") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects when host gpu is required but never negotiated")
step("Verify: rejects when host gpu is required but never negotiated")
var executor = _executor()
executor.host_gpu_required = true
expect(executor.render(_scene([]), _taskbar(), [], 1, 1, "09:41")).to_equal(0)
```

</details>

### render software presents

#### presents an empty scene and retains it, then re-presents unchanged

- presents an empty scene and retains it, then re-presents unchanged
- Verify: presents an empty scene and retains it, then re-presents unchanged
   - Expected: executor.render(_scene([]), _taskbar(), [], 3, 1, "09:41") equals `3`
   - Expected: executor.last_successful_scene_revision equals `3`
   - Expected: executor.render(_scene([]), _taskbar(), [], 3, 1, "09:41") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("presents an empty scene and retains it, then re-presents unchanged")
step("Verify: presents an empty scene and retains it, then re-presents unchanged")
var executor = _executor()
expect(executor.render(_scene([]), _taskbar(), [], 3, 1, "09:41")).to_equal(3)
expect(executor.last_successful_scene_revision).to_equal(3)  # oracle: 3 — named expected value from the requirement
# same revision again: retained plan admitted, no extents marked
expect(executor.render(_scene([]), _taskbar(), [], 3, 1, "09:41")).to_equal(3)
```

</details>

#### keeps minimized and zero-content windows as chrome without surfaces

- keeps minimized and zero-content windows as chrome without surfaces
- Verify: keeps minimized and zero-content windows as chrome without surfaces
   - Expected: executor.render(_scene(windows), _taskbar(), [], 5, 1, "09:41") equals `5`
   - Expected: executor.last_successful_window_rects.len() equals `10`
   - Expected: executor.last_successful_window_rects[4] equals `0`
   - Expected: executor.last_successful_window_rects[9] equals `1`
   - Expected: executor.render(_scene(windows), _taskbar(), [], 6, 1, "09:41") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps minimized and zero-content windows as chrome without surfaces")
step("Verify: keeps minimized and zero-content windows as chrome without surfaces")
var executor = _executor()
val windows = [
    _window("wmin", 10, 10, 64, 48, true),
    _window("wzero", 30, 30, 8, 48, false)]
expect(executor.render(_scene(windows), _taskbar(), [], 5, 1, "09:41")).to_equal(5)
# retained extents are FULL window bounds (chrome included): the
# minimized window records invalid, but the zero-CONTENT window still
# paints chrome across its 8x48 bounds, so its extents stay valid.
expect(executor.last_successful_window_rects.len()).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(executor.last_successful_window_rects[4]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(executor.last_successful_window_rects[9]).to_equal(1)  # oracle: 1 — named expected value from the requirement
# next changed revision walks retained extents past the valid==0 arm
expect(executor.render(_scene(windows), _taskbar(), [], 6, 1, "09:41")).to_equal(6)
```

</details>

#### degrades a window with no content frame but still presents

- degrades a window with no content frame but still presents
- Verify: degrades a window with no content frame but still presents


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("degrades a window with no content frame but still presents")
step("Verify: degrades a window with no content frame but still presents")
var executor = _executor()
expect(executor.render(
    _scene([_window("w1", 10, 10, 64, 48, false)]),
    _taskbar(), [], 2, 1, "09:41")).to_equal(2)
```

</details>

#### degrades on a checksum-invalid content frame

- degrades on a checksum-invalid content frame
- Verify: degrades on a checksum-invalid content frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("degrades on a checksum-invalid content frame")
step("Verify: degrades on a checksum-invalid content frame")
var executor = _executor()
var frame = _frame_for("w1", 2, 56, 12)
frame.checksum = 12345u64
expect(executor.render(
    _scene([_window("w1", 10, 10, 64, 48, false)]),
    _taskbar(), [frame], 2, 1, "09:41")).to_equal(2)
```

</details>

#### degrades on duplicate content frames for one window

- degrades on duplicate content frames for one window
- Verify: degrades on duplicate content frames for one window


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("degrades on duplicate content frames for one window")
step("Verify: degrades on duplicate content frames for one window")
var executor = _executor()
val frames = [_frame_for("w1", 2, 56, 12), _frame_for("w1", 2, 56, 12)]
expect(executor.render(
    _scene([_window("w1", 10, 10, 64, 48, false)]),
    _taskbar(), frames, 2, 1, "09:41")).to_equal(2)
```

</details>

#### rejects a degraded window outright when host gpu is required

- rejects a degraded window outright when host gpu is required
- Verify: rejects a degraded window outright when host gpu is required


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a degraded window outright when host gpu is required")
step("Verify: rejects a degraded window outright when host gpu is required")
var executor = _executor()
executor.host_gpu_required = true
executor.host_gpu_base = 4096u64
expect(executor.render(
    _scene([_window("w1", 10, 10, 64, 48, false)]),
    _taskbar(), [], 2, 1, "09:41")).to_equal(0)
```

</details>

#### presents resolved window content and retains its extents

- presents resolved window content and retains its extents
- Verify: presents resolved window content and retains its extents
   - Expected: executor.last_successful_window_rects.len() equals `5`
   - Expected: executor.last_successful_window_rects[4] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("presents resolved window content and retains its extents")
step("Verify: presents resolved window content and retains its extents")
var executor = _executor()
val win = _window("w1", 10, 10, 64, 48, false)
expect(executor.render(
    _scene([win]), _taskbar(), [_frame_for("w1", 2, 56, 12)],
    2, 1, "09:41")).to_equal(2)
expect(executor.last_successful_window_rects.len()).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(executor.last_successful_window_rects[4]).to_equal(1)  # oracle: 1 — named expected value from the requirement
# moved window at a new revision marks old+new extents (retained lane)
val moved = _window("w1", 30, 30, 64, 48, false)
expect(executor.render(
    _scene([moved]), _taskbar(), [_frame_for("w1", 3, 56, 12)],
    3, 1, "09:41")).to_equal(3)
```

</details>

#### recomposes locally when a stale host target lingers

- recomposes locally when a stale host target lingers
- Verify: recomposes locally when a stale host target lingers
   - Expected: executor.render(_scene([]), _taskbar(), [], 4, 1, "09:41") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("recomposes locally when a stale host target lingers")
step("Verify: recomposes locally when a stale host target lingers")
var executor = _executor()
executor.draw_ir_backend_target = "vulkan"
expect(executor.render(_scene([]), _taskbar(), [], 4, 1, "09:41")).to_equal(4)
```

</details>

#### degrades a provenance-invalid simple-web frame but still presents

- degrades a provenance-invalid simple-web frame but still presents
- Verify: degrades a provenance-invalid simple-web frame but still presents


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("degrades a provenance-invalid simple-web frame but still presents")
step("Verify: degrades a provenance-invalid simple-web frame but still presents")
var executor = _executor()
var frame = _frame_for("w1", 2, 56, 12)
frame.origin_kind = WM_CONTENT_ORIGIN_SIMPLE_WEB
expect(executor.render(
    _scene([_window("w1", 10, 10, 64, 48, false)]),
    _taskbar(), [frame], 2, 1, "09:41")).to_equal(2)
```

</details>

#### degrades the second window sharing a duplicate content uri

- degrades the second window sharing a duplicate content uri
- Verify: degrades the second window sharing a duplicate content uri


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("degrades the second window sharing a duplicate content uri")
step("Verify: degrades the second window sharing a duplicate content uri")
var executor = _executor()
val windows = [
    _window("w1", 2, 2, 64, 48, false),
    _window("w1", 30, 8, 64, 48, false)]
expect(executor.render(
    _scene(windows), _taskbar(), [_frame_for("w1", 2, 56, 12)],
    2, 1, "09:41")).to_equal(2)
```

</details>

### retained plan background identity

#### fails closed to full before any successful frame

- fails closed to full before any successful frame
- Verify: fails closed to full before any successful frame
   - Expected: plan.mode equals `DAMAGE_PLAN_FULL`
   - Expected: plan.fallback_reason equals `DAMAGE_FALLBACK_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed to full before any successful frame")
step("Verify: fails closed to full before any successful frame")
var executor = _executor()
val scene = _scene([])
val plan = executor.retained_scene_damage_plan(scene, "key-a", 1)
expect(plan.mode).to_equal(DAMAGE_PLAN_FULL)
expect(plan.fallback_reason).to_equal(DAMAGE_FALLBACK_INVALID)
```

</details>

#### admits the retained plan on an unchanged revision and matching key

- admits the retained plan on an unchanged revision and matching key
- Verify: admits the retained plan on an unchanged revision and matching key


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits the retained plan on an unchanged revision and matching key")
step("Verify: admits the retained plan on an unchanged revision and matching key")
var executor = _executor()
val scene = _scene([
    _window("w1", 4, 4, 40, 40, false),
    _window("wmin", 8, 8, 40, 40, true)])
val key = engine2d_wm_background_key(scene)
executor.record_successful_scene(scene, key, 5)
# same revision: admitted past the background gate, no extents marked
val same = executor.retained_scene_damage_plan(scene, key, 5)
assert_true(same.planned_pixels >= 0)
```

</details>

#### marks retained old and current extents on a changed revision

- marks retained old and current extents on a changed revision
- Verify: marks retained old and current extents on a changed revision


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("marks retained old and current extents on a changed revision")
step("Verify: marks retained old and current extents on a changed revision")
var executor = _executor()
val scene = _scene([
    _window("w1", 4, 4, 40, 40, false),
    _window("wmin", 8, 8, 40, 40, true)])
val key = engine2d_wm_background_key(scene)
executor.record_successful_scene(scene, key, 5)
# one valid + one invalid retained record: the while walk takes both
# arms of the valid flag, the current pass both arms of minimized.
val changed = executor.retained_scene_damage_plan(scene, key, 6)
assert_true(changed.dirty_pixels > 0)
```

</details>

#### fails closed to full when the background key changes

- fails closed to full when the background key changes
- Verify: fails closed to full when the background key changes
   - Expected: plan.mode equals `DAMAGE_PLAN_FULL`
   - Expected: plan.fallback_reason equals `DAMAGE_FALLBACK_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed to full when the background key changes")
step("Verify: fails closed to full when the background key changes")
var executor = _executor()
val scene = _scene([])
executor.record_successful_scene(scene, "key-a", 1)
val plan = executor.retained_scene_damage_plan(scene, "key-b", 2)
expect(plan.mode).to_equal(DAMAGE_PLAN_FULL)
expect(plan.fallback_reason).to_equal(DAMAGE_FALLBACK_INVALID)
```

</details>

### host image resource staging

#### stages a resolved host image before the required-degraded reject

- stages a resolved host image before the required-degraded reject
- Verify: stages a resolved host image before the required-degraded reject


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("stages a resolved host image before the required-degraded reject")
step("Verify: stages a resolved host image before the required-degraded reject")
# host_gpu_base set: the resolved w1 frame is pushed into the host
# image resource list (line 354 true arm — pure staging, no mmio),
# then the degraded w2 window trips the fail-closed required gate
# BEFORE any ivshmem submit could touch mmio.
var executor = _executor()
executor.host_gpu_base = 4096u64
executor.host_gpu_required = true
val windows = [
    _window("w1", 2, 2, 64, 48, false),
    _window("w2", 30, 8, 64, 48, false)]
expect(executor.render(
    _scene(windows), _taskbar(), [_frame_for("w1", 2, 56, 12)],
    2, 1, "09:41")).to_equal(0)
```

</details>

### render composition edge shapes

#### still presents a zero-size scene through the software lane

- still presents a zero-size scene through the software lane
- Verify: still presents a zero-size scene through the software lane
   - Expected: executor.render(scene, _taskbar(), [], 9, 1, "09:41") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("still presents a zero-size scene through the software lane")
step("Verify: still presents a zero-size scene through the software lane")
var executor = Engine2dWmFrameExecutor.create(
    Engine2D.create_with_backend(8, 8, "cpu"),
    FramebufferDriver.empty(), 0, 0)
val scene = SharedWmScene(width: 0, height: 0, backend: "cpu",
                          windows: [],
                          background: shared_wm_background_color(0xff101010u32))
expect(executor.render(scene, _taskbar(), [], 9, 1, "09:41")).to_equal(9)
```

</details>

#### presents a fully populated taskbar composition

- presents a fully populated taskbar composition
- Verify: presents a fully populated taskbar composition
   - Expected: executor.render(_scene([]), _full_taskbar(), [], 8, 1, "") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("presents a fully populated taskbar composition")
step("Verify: presents a fully populated taskbar composition")
var executor = _executor()
expect(executor.render(_scene([]), _full_taskbar(), [], 8, 1, "")).to_equal(8)
```

</details>

#### resolves two windows with distinct content uris

- resolves two windows with distinct content uris
- Verify: resolves two windows with distinct content uris
   - Expected: executor.last_successful_window_rects.len() equals `10`
   - Expected: executor.last_successful_window_rects[4] equals `1`
   - Expected: executor.last_successful_window_rects[9] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves two windows with distinct content uris")
step("Verify: resolves two windows with distinct content uris")
var executor = _executor()
val windows = [
    _window("w1", 2, 2, 64, 48, false),
    _window("w2", 30, 8, 64, 48, false)]
val frames = [_frame_for("w1", 7, 56, 12), _frame_for("w2", 7, 56, 12)]
expect(executor.render(_scene(windows), _taskbar(), frames,
                       7, 1, "09:41")).to_equal(7)
expect(executor.last_successful_window_rects.len()).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(executor.last_successful_window_rects[4]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(executor.last_successful_window_rects[9]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### still presents under an unknown material target name

- still presents under an unknown material target name
- Verify: still presents under an unknown material target name
   - Expected: executor.render(_scene([]), _taskbar(), [], 11, 1, "09:41") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("still presents under an unknown material target name")
step("Verify: still presents under an unknown material target name")
var executor = _executor()
# The advanced software lane renders by command kind, not by target
# string, so an unknown target must not black-screen the frame.
executor.draw_ir_backend_target = "no-such-backend"
executor.local_draw_ir_backend_target = "no-such-backend"
expect(executor.render(_scene([]), _taskbar(), [], 11, 1, "09:41")).to_equal(11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-OS-COMPOSITOR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `93becc57c9e10e062b385194b94cb699f7f3ac4f4ce23df52cd1b22a9b9ef549`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93becc57c9e10e062b385194b94cb699f7f3ac4f4ce23df52cd1b22a9b9ef549`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93becc57c9e10e062b385194b94cb699f7f3ac4f4ce23df52cd1b22a9b9ef549`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects host, cpu_simd and cpu targets by gate order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires local recompose only when targets differ' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps negative dims in the fail-closed full plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
