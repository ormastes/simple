# GPU backend probe-then-create TOCTOU makes offload gates flaky and vacuous

- **Date:** 2026-08-04
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  and landed, together with both legacy mirrors (see Campaign below). The family is
  **larger than the seven** — a second sweep found 5 more instances, still OPEN, the
  biggest of which (`cuda_strict_spec.spl`) has ~19 prediction-gated examples.
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

| `1b3ce9a9356` | `03_system/gui/draw_backend_matrix/draw_backend_matrix_spec.spl` + `proc_draw_combo_spec.spl` | matrix: 8/8 unconstrained, **6/6 red** at `ulimit -n 44` — `✗ vulkan: real device draw-apply…` / `semantic: called unwrap on Err: backend unavailable: vulkan`. That message is a second defect the TOCTOU exposed: `assert_true(created.is_ok())` does NOT abort the example body, so the unconditional `created.unwrap()` on the next line hard-errored instead of failing cleanly. combo does not reproduce at fd 44 at all — the spec cannot even LOAD (`1 total, 0 passed, 1 failed`, no examples executed, confirmed identical on the pre-fix base, so it is the harness not the spec); sweeping 64/96/128/192/256 found **fd 96** is the limit that reaches the lane, reproducing 6/6. Post-fix 8/8 and 12/12, with 0 GPU-PROVEN and explicit skips. |
| `32b9593a6cf` | revert of `7251dde66f0` | See "A false broken-landing call" below. |

Independently re-verified in a separate worktree at the landed tip, rather than
taken on report: `engine2d_backend_matrix` 16/16 (1 GPU-PROVEN),
`backend_opencl_facade` 12/12 (0 GPU-PROVEN, OpenCL genuinely unavailable),
`vulkan_strict` and its legacy twin 17/17 (8 GPU-PROVEN each, byte-identical).

### A false broken-landing call — sync EVERY path a commit touched

Worth recording because the failure mode is convincing and cost a revert.

After `1b3ce9a9356` landed, a reviewer (me) copied the two SPEC files out of the
tip into a working tree and ran them. They failed with
`semantic: function assert_provenance_invariants not found`, on 6 call sites, in
both specs — which reads exactly like a landing that shipped calls to undefined
functions. A grep of the shared helper appeared to confirm it. `7251dde66f0` was
then landed to "repair main" by adding ~140 lines of spec-local definitions.

The premise was wrong. `1b3ce9a9356` touched **three** paths, not two — both
specs AND `test/helpers/gpu_draw_event_shared.spl` — and defined all four helpers
in that shared file. Only the two specs had been synced, so the helper was still
at its base revision (`02dc7774aba` in the working tree vs `b0cf937ebc4` at tip,
which defines all four). The failure was an artifact of a partially synced tree
and described a state that never existed on main. The confirming grep was run
against the same stale file, so it agreed with the error rather than checking it.

Established on a fully synced tree before reverting: true main WITH the
duplicates 8/8 and 12/12; specs restored to `1b3ce9a9356` with the shared helper
at tip, also 8/8 and 12/12 — so the helper alone suffices and the additions were
pure redundancy. Reverted in `32b9593a6cf`; the shared helper is untouched by
that revert.

Rules that would have caught it:
- When judging whether a landed commit is self-consistent, sync **every path that
  commit touched** (`git diff-tree --no-commit-id --name-only -r <sha>`), not just
  the ones under investigation.
- A "function not found" error is exactly the shape a stale sibling file produces.
  Before concluding a landing is broken, check the symbol at the TIP
  (`git show <tip>:<path>`), never in the working tree.
- Two pieces of evidence drawn from the same stale file are one piece of evidence.

### Separate defect found in passing — per-process Vulkan resource leak

Not a TOCTOU and NOT fixed here. `vulkan_strict_spec` exited non-zero while all
19 examples printed ✓; the child process itself exited 1. Bisected with dedicated
loop specs: 15 Engine2D vulkan create+render+shutdown cycles exit 0, **20 cycles
exit 1**; 30 `probe_backend` calls alone exit 0; 6 probes + 14 creates exit 1. So
the leak is in the create/shutdown cycle, not the probe. The spec pre-fix issued
19 probes + 11 creates; the fix drops it to 6 probes + 12 creates, which happens
to clear the threshold — meaning the underlying backend leak is still there and
will resurface for any spec that creates ~20 vulkan backends in one process.

**FIXED 2026-08-05 — and the "~20" estimate did not reproduce.** Measured on
TITAN RTX + RTX A6000, the first failing create is **#63** — the 64th device,
the driver's per-process device ceiling. It is #63 for BOTH shapes: the bare
`VulkanBackend.create()+init()+shutdown()` loop and the heavier `Engine2D`
create+clear+draw+readback+present+shutdown cycle. That the two agree is the
tell: the exhausted resource is the DEVICE COUNT, not any per-device object, so
the ceiling does not move with what the backend touches between creates. The
failure mode is `init()` returning false with
`last_error = "Vulkan shared session initialization failed: runtime-init"` while
`rt_vulkan_last_error()` is EMPTY and `rt_vulkan_is_available()` still reports 1
— a silent exhaustion that reads like a host problem. The process then
segfaults at exit (139) while tearing down 63 stranded devices.

Root cause: `rt_vulkan_init_fn`
(`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`) created a fresh
VkInstance + VkDevice + VkCommandPool on EVERY call and then overwrote the
`VK_STATE` singleton. `VulkanState` holds raw handles and has no `Drop` impl, so
the previous instance/device/command pool — and every buffer, shader module,
compute pipeline, descriptor pool and command buffer recorded in that state —
were orphaned with no `vkDestroy*` call. Nothing on the `.spl` side compensates:
`VulkanSession._cleanup()` destroys the shaders and pipelines it owns by handle
and then merely ZEROES `instance` / `device` / `command_pool` / `pipeline_cache`
/ `allocator`; it never calls `vulkan_sffi_shutdown()`.

So the answer to "does the probe path call shutdown?" is YES and it was never
the culprit: `Engine2D.probe_backend`'s vulkan arm does call `b.shutdown()` on
success. The abandonment was one layer down, in the runtime extern. What the
probe path DID contribute is cost — a probed lane ran two full create/init
cycles and therefore stranded two devices.

Fix (not a cap, not a retry — it stops ACQUIRING the duplicate):
`rt_vulkan_init_fn` now returns the live singleton when `VK_STATE` already holds
a state with a non-null device, exactly matching the compiled runtime's
`rt_vulkan_init` (`vulkan_graphics_runtime_core.rs`), which has always
short-circuited on `state.device.is_some()`. The interpreter extern was the
divergent sibling of an already-correct implementation. This also removes the
probe-then-create double cost at the root: probe and create now share one
instance and one device.

Control-arm evidence that identifies the leaked object set: the same loop with
an explicit `vulkan_sffi_shutdown()` per iteration ran 200/200 clean and exited
0 — i.e. the stranded objects are exactly what `rt_vulkan_shutdown` releases.

Provenance is unaffected. `_web_gpu_readback_device_proven` requires
`source == "device_readback"`, and only `backend_vulkan.spl:823` emits that
source, from a live session. `backend_handle` stays the per-surface
`d_framebuffer` (allocated per `init_with_session`, freed in `shutdown`);
`device_identity` is `session.device`, which reuse makes CONSTANT across engines
instead of distinct — but the predicate tests `> 0`, never uniqueness, and a
CPU-produced frame never reaches that arm at all. No new pass path is created.

Family sweep — vulkan was the only offender. CUDA memoizes `cuInit` behind
`CUDA_INIT_RESULT.get_or_init` (one acquire per process). WebGPU's and OpenCL's
interpreter externs are inert stubs that return 0 and acquire nothing (which is
also why OpenCL context creation reports `context=0` on this host). Metal is
macOS-only and inert on Linux, so it is FLAGGED as unverified here rather than
claimed clean. Baremetal/virtio_gpu acquire no runtime handles on this path.
`VK_STATE` is the only `Mutex<Option<...>>` global in the interpreter externs
that gets replaced rather than reused.

Regression gate: `test/02_integration/rendering/vulkan_instance_reuse_spec.spl`.
NOTE: the fix lives in the Rust seed, so it is only live in `bin/simple` after a
seed rebuild + redeploy.

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

#### SCOPE — the tooth applies to STRICT creates only, NOT to name-resolving façades

This tooth is correct for a spec that drives `Engine2D.create_with_backend_strict`
directly, and it is a **FALSE RED** for a spec that goes through the browser-engine
façade. Applying it blindly to the wrong lane costs a clean tree 3/3 red runs at
`ulimit -n 44`.

- **Strict-create lanes** (e.g. `backend_probe_spec`, `vulkan_strict_spec`): a
  strict create never falls back. When the device is gone the CREATE FAILS and the
  spec takes the structured-failure path, so a successful strict GPU create really
  does hold a device, and `cpu_mirror` really is a bookkeeping defect. Verified:
  `backend_probe_spec` at `ulimit -n 44`, 5/5 runs green with `device_readback` as
  the ONLY source observed — `cpu_mirror` never appears.
- **Façade lanes** (e.g. `web_render_pixel_backend_queue_spec`): `backend_vulkan.spl`
  has **no `cpu_mirror` emitter at all**. There, `cpu_mirror` comes from
  `simple_web_engine2d_renderer.spl:1153`, and the sticky-flag justification does
  not transfer. On such a lane `cpu_mirror` is an environmental divergence, not a
  defect signal, and must be disclosed rather than failed.

Corollary for sabotage: `backend_vulkan.spl:824` is NOT a universal probe. On the
façade lane the frames return through a different branch (L837) and the L824
sabotage has **NO EFFECT** — a green result there would read as "over-relaxed"
when in truth the sabotage never touched the executed path. Prefer a
source-label-independent failability probe (zeroing the handle/identity the
assertion actually reads) and confirm your sabotage lies on the executed path.

### Separate production defect — two independent backend resolvers disagree

Disclosed but NOT fixed; worth filing in its own right. On the browser-engine
path the backend name is resolved **twice, independently**:
`web_render_resolved_engine2d_backend_name` (`web_render_pixel_backend.spl:321`)
versus the renderer's own `_resolved_render_backend`
(`simple_web_engine2d_renderer.spl:1146`). Under fd pressure they disagree: the
façade stamps `vulkan` and emits a full drained queue receipt while the renderer
rasterises on the CPU and reports `cpu_mirror` (L1153). This is the same
resolve-then-use gap as the spec-level defect, but living in production code.

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

**Re-examined — "no create involved" is true but understates the consequence.**
`val chosen = simple_web_engine2d_resolved_backend_name(...)` followed by
`expect(probe(chosen).status == BackendStatus.Initialized).to_equal(true)` is a
probe-vs-probe gap: the resolver's internal probe and the spec's re-probe are two
independent device queries, so under fd pressure the re-probe can fail while the
resolver said vulkan. That is a genuine FALSE RED. There is no vacuous-green half
(the assertion is unconditional), so it is the lowest-severity member of the
family — but it is a member, not a non-instance.

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
