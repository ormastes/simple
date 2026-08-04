# GPU backend probe-then-create TOCTOU makes offload gates flaky and vacuous

- **Date:** 2026-08-04
- **Status:** parity spec FIXED; sibling sweep IN PROGRESS (see Campaign below).
  The family is **larger than the seven** originally listed — a second sweep found
  5 more instances, the biggest of which (`cuda_strict_spec.spl`) has ~19
  prediction-gated examples.
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

## Campaign — sibling fixes landed

Each fix follows the parity spec's structure: nothing asserted from the probe,
probe/create divergence disclosed on a `[toctou]` line, provenance invariants
asserted unconditionally, and `GPU-PROVEN` / `GPU BRANCH SKIPPED` disclosure so a
device-unavailable pass cannot be misread as a GPU pass. Every one is
sabotage-verified to still go red.

| Commit | Spec | Evidence |
|---|---|---|
| `4cb2434a48c` | `05_perf/graphics_2d/backend_probe_spec.spl` + legacy twin | Pre-fix false red reproduced **6/6** at `ulimit -n 44` (`✗ executes Vulkan SPIR-V … expected false to equal true`). Post-fix 6/6 green across 6 runs with the `[toctou]` disclosure, GPU-PROVEN 3→1. Sabotage: `4 passed, 2 failed`, exit 1. |
| `c774930660` | same pair — follow-up | Widened the readback vocabulary (see below); failability re-verified after the relaxation. |
| `04c5276fb00` | `02_integration/gpu/engine2d_backend_matrix_spec.spl` | **Vacuous green reproduced 3/3**: byte-identical `14 total, 14 passed, 0 failed` whether vulkan was `Initialized` or `Unavailable`, with **0 GPU-PROVEN either way** — the old spec read `read_pixels()` with no provenance at all. The same sabotage against the PRE-fix spec still gave `14/14 PASS, exit 0`; post-fix it gives `15 passed, 1 failed`, exit 1. Strictly harder, not relaxed. |
| `8622c8f2936` | `01_unit/lib/gpu/engine2d/backend_opencl_facade_spec.spl` | Found the spec's device examples were **dead code**: both called `strict_failure_without_fallback()`, which exists only on engine3d's probe type, so every run aborted with a semantic error (`12 total, 10 passed, 2 failed`) and the probe/create branch had NEVER executed. Fixed the dead call, then the TOCTOU. OpenCL is unavailable on this host, so the OpenCL device branch is unreachable and its own sabotage is unobservable — assertion logic proven via CUDA instead. Stated rather than papered over. |
| `e367ef0f50c` | `05_perf/graphics_2d/backend_probe_spec.spl` + legacy twin | Restored the owned-create tooth (below); proven by a SECOND sabotage. |
| `703b022cb94` | `01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl` | **Both directions reproduced.** False red 3/3 at `ulimit -n 44`: the probe went Unavailable while the create had already served a real vulkan frame, so the spec took the software else-branch and asserted an empty queue payload against a genuine drained GPU packet. Vacuous green reproduced by hiding the Vulkan ICD (`VK_ICD_FILENAMES=/nonexistent`), giving a `✓` line byte-identical to the real-GPU pass. New tooth: the queue receipt was synthesized from the resolved backend NAME alone, so a GPU-named backend serving a CPU-sourced frame now fails closed as a fabricated device receipt. Note: a **pre-existing unrelated red** in this file (Draw IR material fallback, `expected 0 to equal 64`) is present on `main` and untouched. |

| `c099703b607` | `02_integration/rendering/vulkan_strict_spec.spl` + legacy twin | **The starkest vacuous green in the family: the fd-starved run was GREENER than the healthy one.** Unconstrained `20 total, 19 passed, 1 failed` in 18.7 s; at `ulimit -n 44` `19 total, 19 passed, 0 failed`, exit 0, in 7.1 s — every device branch skipped on the probe's say-so, ~11.7 s of real GPU work silently absent, and it reads as a cleaner pass than the real one. Post-fix: 17/17 with **8 GPU-PROVEN** unconstrained, and 17/17 with **0 GPU-PROVEN / 10 SKIPPED** at fd44. Both sabotages give `17 total, 9 passed, 8 failed`, exit 1. Legacy twin was one whole example weaker (it lacked the direct `VulkanBackend` checked-clear-and-rect example); both now byte-identical. |

Independently re-verified in a separate worktree at the landed tip, rather than
taken on report: `engine2d_backend_matrix` 16/16 (1 GPU-PROVEN),
`backend_opencl_facade` 12/12 (0 GPU-PROVEN, OpenCL genuinely unavailable),
`vulkan_strict` and its legacy twin 17/17 (8 GPU-PROVEN each, byte-identical).

### Separate defect found in passing — per-process Vulkan resource leak

Not a TOCTOU and NOT fixed here. `vulkan_strict_spec` exited non-zero while all
19 examples printed ✓; the child process itself exited 1. Bisected with dedicated
loop specs: 15 Engine2D vulkan create+render+shutdown cycles exit 0, **20 cycles
exit 1**; 30 `probe_backend` calls alone exit 0; 6 probes + 14 creates exit 1. So
the leak is in the create/shutdown cycle, not the probe. The spec pre-fix issued
19 probes + 11 creates; the fix drops it to 6 probes + 12 creates, which happens
to clear the threshold — meaning the underlying backend leak is still there and
will resurface for any spec that creates ~20 vulkan backends in one process.

### The owned-create tooth — do not relax this away

Moving the device-label claim into `_assert_provenance_invariants` makes the
device checks conditional ON the source. That silently converts a GPU backend
reporting `cpu_mirror` from a FAILURE into a disclosed skip — more relaxed than
the parity spec. Where the spec **owns its create**, restore it:

```simple
expect(readback.source == "cpu_mirror").to_equal(false)
```

A GPU backend that degrades sets the STICKY `cpu_fallback_used` flag with a
recorded reason (`backend_vulkan.spl:219-220`, `mark_cpu_fallback` L395) and
reports `cpu_fallback`. So a successful strict GPU create reporting `cpu_mirror`
is a silent CPU reclassification — a bookkeeping defect, not device loss — and
must fail. Genuine device loss still passes, because it surfaces as
`cpu_fallback`, which stays a disclosed skip. That is exactly where the
known-residual boundary belongs.

Second sabotage that proves this tooth is not vacuous, and which every spec in
this family should be run against: relabel `backend_vulkan.spl:824`
`"device_readback"` -> `"cpu_mirror"`, i.e. a real device frame reported as a CPU
mirror. On `backend_probe_spec.spl` it gives `6 total, 4 passed, 2 failed`,
exit 1.

Related trap, found on the pixel-queue spec: check whether the spec's device
proof rests on a **name-derived** signal (the resolved backend NAME) rather than
a **device-derived** one (the readback's source/handle/identity). A receipt
synthesized from the backend name alone will happily stamp GPU evidence onto a
CPU-served frame.

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

## Sibling instances — FOUND BY THE SECOND SWEEP (beyond the original seven)

The original list was one lane's sweep and was not the whole family. A second,
independent sweep over all of `test/` (including the legacy mirror trees) found
these, each verified by reading the probe site and the separate create site:

| File | Shape | Directions |
|---|---|---|
| `test/02_integration/rendering/cuda_strict_spec.spl` | **25** `probe_cuda()` calls, **22** independent `create_with_backend_strict(…,"cuda")`, **19** `if probe.is_usable()` branches. `if not probe.is_usable():` → `expect(result.is_ok()).to_equal(false)`; `if probe.is_usable():` → `expect(result.is_ok()).to_equal(true)` | BOTH; by far the largest blast radius in the family |
| `test/02_integration/rendering/webgpu_strict_spec.spl` | `probe_webgpu()` L88/94/102/115 → creates L96/104/117; `if probe.is_ok():` then `expect(result.is_ok()).to_equal(true)` | BOTH |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl` | `probe_cuda_2d()` L425 → create L427; `if probe.status != Initialized:` → `expect(result.is_ok()).to_equal(false)` | BOTH |
| `test/02_integration/os/crypto/x25519mlkem768_backend_matrix_spec.spl` | Reverse order: the executor create+run happens first, then `if cuda_available():` / `metal_sffi_is_available()` gates the device assertions on a **separate later** capability call | VACUOUS GREEN dominant |
| `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` | `StrictBackendFactory.strict().create_backend("cuda")` is a real create, but `if cuda_available():` gates the status assertions on a **second independent** capability call | FALSE RED both arms; not vacuous, so lower severity |

Legacy-mirror status for the newly-found five — the drift is systemic, not
incidental (`webgpu_strict` is a byte-identical copy; the other three have
DIVERGED from their modern twins and must be reconciled, not blindly overwritten):

| Modern | Legacy twin | Delta |
|---|---|---|
| `02_integration/rendering/cuda_strict_spec.spl` | `integration/rendering/cuda_strict_spec.spl` | 13 lines differ |
| `02_integration/rendering/webgpu_strict_spec.spl` | `integration/rendering/webgpu_strict_spec.spl` | identical |
| `01_unit/…/backend_cuda_renderbackend_spec.spl` | `unit/…/backend_cuda_renderbackend_spec.spl` | **342 lines differ** |
| `01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` | `unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` | 19 lines differ |

**Not an instance, despite matching the grep:** `test/helpers/gpu_draw_event_shared.spl`
`probe_backend(backend, caps)` (L68) does **no device work at all** — it is a pure
function over a `BackendCaps` struct passed in, and `caps_for()` (L133-142)
SYNTHESIZES those caps from a requested backend enum. There is no time-of-check
to time-of-use gap in it, and it must not be "fixed" — it has 7 callers.

## Checked and NOT instances

Mild: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_backend_resolver_spec.spl`
(12, 24, 39) re-validates one prediction with another; no create involved.

Checked and SAFE, re-verified independently by the second sweep:
`web_gpu_first_present_decision_spec.spl` (L74 probe is asserted directly; L142
branches on the real receipt), `web_showcase_full_gpu_offload_spec.spl` (L321
branches on `_probe_source_cache`, which IS the executed readback source),
`web_engine2d_metal_offload_spec.spl` (branches on `is_macos()` and on
`res.gpu_complete` from the real run), `engine2d_backend_spec.spl` (probes
asserted directly; the create is asserted on `engine.backend_name()`),
`simple_web_engine2d_renderer_spec.spl` (the resolved name is fed INTO the
render, then outputs are compared).

**Correction:** `backend_probe_strict_spec.spl` was previously on this SAFE list
and does **not** belong there — see the second-sweep table above. It is the same
defect class (a second, independent `cuda_available()` gating assertions about a
real create), merely lower severity because both arms assert rather than skip.

## The readback source vocabulary is WIDER than eight labels

The parity fix enumerated eight source labels and failed closed on anything else.
That enumeration is incomplete, and the gap is a live false-red generator. Three
more labels are produced by the engine2d backends:

| Label | Produced at | Correct class |
|---|---|---|
| `device_identity_unknown` | `backend_cuda.spl:1050` — the device→host copy SUCCEEDED but `cuda_device_identity()` returned <= 0 | no-frame |
| `preflight_rejected` | `draw_ir_adv.spl:1970,1974` | no-frame |
| `framebuffer_surface` | `backend_baremetal.spl:427` — a real scanout surface | device (but never device-PROVEN, since `_device_proven` requires the `device_readback` label specifically) |

Two more exist above the backend layer and are reachable only by specs that go
through the **browser engine**, not by specs driving `Engine2D` backends directly:

| Label | Produced at | Correct class |
|---|---|---|
| `unavailable` | `simple_web_layout_engine2d_fast.spl:704,720` — carries `[]` | no-frame |
| `cache` | `simple_web_engine2d_renderer.spl:172` — carries `self.last_pixels`, a REAL frame of **unattributed** provenance | neither device nor CPU nor no-frame: it needs a 4th *unattributed* class. Classing it no-frame is wrong (it has a frame); classing it device is wrong (nothing proves a device made it) |

The authoritative way to enumerate this, rather than trusting any list including
this one, is to grep the actual argument values at the construction sites:

```sh
/usr/bin/grep -rhoE 'engine2d_readback(_with_handle|_with_identity)?\([^,]+, *"[a-z_]+"' src/lib/ \
  | /usr/bin/grep -oE '"[a-z_]+"$' | sort -u
```

Each spec should classify the labels reachable from the surface it actually
exercises and fail closed on the rest — adding unreachable labels is dead code.

Two consequences for every spec in this family, both of which bit
`backend_probe_spec.spl` after its first fix and were repaired in `c774930660`:

1. The fail-closed "UNKNOWN READBACK SOURCE" arm fires on a legitimate host
   condition unless these are classified.
2. **Every no-frame source carries an EMPTY pixel array.** Any unconditional
   frame-content assertion (`pixels.len() == W*H`, pixel colour checks, CPU-oracle
   parity loops) therefore false-reds on them. Those assertions must be gated on
   `_source_is_no_frame(source)` with an explicit
   `FRAME ASSERTIONS SKIPPED … proves NOTHING about rendering correctness` line —
   and gated no more narrowly than that, so they still run on every source that
   DID produce a frame, on whatever backend served it.

Failability must be re-verified after making this relaxation, because it is
exactly the kind of change that can quietly remove teeth. For
`backend_probe_spec.spl` the sabotage still gave `6 total, 4 passed, 2 failed`,
exit 1, the same red as before the widening.

## Gates

`web_engine2d_gpu_offload_parity_spec.spl` 17/17 ·
`web_gpu_first_present_decision_spec.spl` 7/7 ·
`web_gpu_present_paint_coverage_spec.spl` 23/23 ·
`web_showcase_full_gpu_offload_spec.spl` 13/13
