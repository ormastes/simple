# GPU backend probe-then-create TOCTOU makes offload gates flaky and vacuous

- **Date:** 2026-08-04
- **Status:** parity spec FIXED; 7 sibling specs OPEN
- **Area:** rendering / engine2d GPU offload
- **Fixed here:** `test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl`

## Defect

A spec asks a capability probe which GPU backend is available, stores the answer,
and then branches its GPU-only assertions on that stored answer. The actual
device create happens later and independently:

- `simple_web_engine2d_resolved_backend_name()` →
  `Engine2D.probe_backend(w, h, "vulkan")` → `VulkanBackend.create()` + `init()`
  + `shutdown()`. Returns `"vulkan"` or `"software"`.
- `Engine2D.create_requested_backend(w, h, "vulkan")` → a **second, independent**
  `VulkanBackend.create()` + `init()`.

There is no cache between them. The probe answer is a prediction, and under host
contention it does not survive to the create. Both failure directions corrupt the
gate:

- **False RED** — probe says `vulkan`, create then fails, the presenter returns
  `cpu_fallback`, and the spec's `if _lane_is_gpu(lane)` branch asserts
  `source == "device_readback"`. The code under test is fine; the device went
  away. Originally observed as:
  `[offload-provenance] lane=vulkan source=cpu_fallback handle=0 identity=nil`
- **Vacuous GREEN** — probe says `software`, the GPU branch never runs, and the
  spec reports a clean pass that is textually indistinguishable from a real GPU
  pass.

## Reproduction

`ulimit -n 44` perturbs `vkCreateInstance`/device init without disabling Vulkan,
which is exactly the probe-vs-create race. Host: 2x NVIDIA (TITAN RTX, RTX A6000),
Vulkan 1.4.312. Binary: Rust bootstrap seed.

Probe-then-create divergence, 6 consecutive runs, 6/6:

```
[toctou] iter=0 probe=vulkan create=create_failed  <-- DIVERGENCE
[toctou] divergences=1 of 12
```

Vacuous green at the spec level (pre-fix, same `ulimit -n 44`) — note the header
claims vulkan while the provenance line shows software, and it still reads 17/17:

```
[offload-lane] selected lane: vulkan
[offload-provenance] lane=software source=cpu_mirror handle=0 identity=nil
Results: 17 total, 17 passed, 0 failed
```

20 concurrent spec runs on an unconstrained host did **not** reproduce it
(20/20 device_readback); process contention alone is not sufficient.

## Fix applied to the parity spec

Nothing is asserted from the probe. Every GPU assertion branches on what the
readback actually reports, and the honest-provenance invariants are asserted on
**every** outcome and lane instead of only inside the GPU branch — so the spec is
strictly harder to pass than before, not easier.

- `_assert_provenance_invariants()` — unconditional. `source == "device_readback"`
  obliges `handle > 0`, `identity > 0`, `pixel_count == frame`. A CPU source must
  not be device-sourced and must not satisfy `_device_proven`. An unrecognised
  source fails closed.
- `_report_outcome()` — prints `GPU-PROVEN` or an explicit
  `GPU BRANCH SKIPPED ... proves NOTHING about the GPU offload path`.
- Closing `RUN VERDICT` lines state the reading rule: the run's GPU evidence is
  exactly the set of `GPU-PROVEN` lines; a pass with none of them does not attest
  the GPU path. `grep 'GPU-PROVEN'` separates a real pass from a skipped one.
- `direct-lane` owns its create, so it additionally requires that a **vulkan
  create that succeeded** never returns `cpu_mirror` — VulkanBackend reports
  `cpu_fallback` (with a recorded reason) whenever it degrades, so a silent CPU
  reclassification is a bookkeeping defect and fails. Genuine device loss still
  passes because it surfaces as `cpu_fallback`.

Deliberately **not** asserted: `handle == 0` / `identity == 0` on CPU sources.
Under fd exhaustion the seed surfaces those fields as nil rather than 0 (visible
as `identity=nil` in the spec's own provenance line), so equality there is a
host-condition false red. The two predicates above carry the real claim.

A module-level `var` tally was tried for the RUN VERDICT and **silently did not
work**: writes made inside an `it` body were not visible when read back in the
same body, so the counters stayed 0 while three examples had reported
`GPU-PROVEN`. It printed a verdict contradicting its own run. Removed — run-level
evidence is carried by the per-example lines.

## Sabotage proof (the spec can still fail)

`backend_vulkan.spl:824`, `self.session.device` → `0`, so a real device readback
carries a fabricated identity:

```
Results: 17 total, 15 passed, 2 failed
  ✗ lane readback carries genuine provenance and matches the cpu oracle
      expected false to equal true
  ✗ explicit gpu-paint readback on the lane matches the cpu truth
      expected subject to be truthy, got 0
spec failure: 2 of 17 example(s) failed (exit 1)
```

Restored → 17/17 with three `GPU-PROVEN` lines. Verified both before and after
the CPU-path relaxation, so the relaxation did not cost failability.

### Known residual

A vulkan lane that constructs and then reports `cpu_fallback` is treated as a
skip, not a red, because it is indistinguishable from genuine device loss — which
is the very condition being fixed. This is bounded by disclosure: such a run
prints `GPU BRANCH SKIPPED` and produces no `GPU-PROVEN` line, so it cannot be
read as a GPU pass. Tightening it would require the backend to expose whether the
create succeeded separately from whether the device served the frame.

## Sibling instances — OPEN

Same probe-then-create shape, GPU assertions still driven by the prediction:

| File | Probe | Prediction-driven branch |
|---|---|---|
| `test/05_perf/graphics_2d/backend_probe_spec.spl` | 24, 74, 103 | 34→36-45; 75→77,85-87 |
| `test/02_integration/rendering/vulkan_strict_spec.spl` | 56-58 | 121→123, 140→143, 189→192,210-212 |
| `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl` | 106 | 108→110-119 |
| `test/03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl` | 181 | 182→189-192 |
| `test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl` | 146 | 147→154-157, 172-176 |
| `test/01_unit/lib/gpu/engine2d/backend_opencl_facade_spec.spl` | 308 | 317→319-325 |
| `test/02_integration/gpu/engine2d_backend_matrix_spec.spl` | 105 | 110→113 |

Legacy mirrors with the identical defect:
`test/perf/graphics_2d/backend_probe_spec.spl` (24, 73, 102),
`test/integration/rendering/vulkan_strict_spec.spl` (55; 121-123, 140-143).

Mild: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl`
(12, 24, 39) re-validates one prediction with another; no create involved.

Checked and SAFE: `web_gpu_first_present_decision_spec.spl` (branches on the
returned decision string), `web_showcase_full_gpu_offload_spec.spl` (guards are
fail-closed in the CPU direction), `web_engine2d_metal_offload_spec.spl`,
`backend_probe_strict_spec.spl`, `engine2d_backend_spec.spl`,
`simple_web_engine2d_renderer_spec.spl`.

## Gates

`web_engine2d_gpu_offload_parity_spec.spl` 17/17 ·
`web_gpu_first_present_decision_spec.spl` 7/7 ·
`web_gpu_present_paint_coverage_spec.spl` 23/23 ·
`web_showcase_full_gpu_offload_spec.spl` 13/13
