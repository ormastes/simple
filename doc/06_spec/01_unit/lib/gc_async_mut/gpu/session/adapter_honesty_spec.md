# GPU Backend / Session Adapter Honesty (Lane A3, sites 11-20)

> `doc/04_architecture/ui/wm_host_platform_matrix.md` cluster 3 named ten

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Backend / Session Adapter Honesty (Lane A3, sites 11-20)

`doc/04_architecture/ui/wm_host_platform_matrix.md` cluster 3 named ten

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`doc/04_architecture/ui/wm_host_platform_matrix.md` cluster 3 named ten
false-success sites across the WebGPU engine2d backend, the DXVK/Vulkan ICD
translation chain, and the five session adapters (metal/webgpu/vulkan/cuda/
cpu): capability flags and success sentinels that were never backed by a real
device. `doc/03_plan/ui/wm_platform_honesty_agent_lanes.md` lane A3 fixes them
to honest refusal. This spec is A3's gate: every assertion below fails RED
against the pre-fix code and passes GREEN against the fix (verified by
sabotage, see the lane report).

## Scope and Preconditions

Runs entirely on this Linux host — no macOS/Windows claims are made (rule 4 of
the lane plan: this host cannot execute those paths, so any assertion about
them is out of scope here). Metal is Apple-only, so every metal assertion
below is inherently a "false on this host" refusal check, not a green runtime
claim for macOS.

## Compatibility and Limitations

The vulkan ICD assertions use an invariant (`is_ok == (leaf == "dlopen")`)
rather than forcing a "no library" host state, because this host has a real
`/usr/lib/x86_64-linux-gnu/libvulkan.so.1` and the leaf probe is a private
implementation detail not injectable from a spec. The invariant is still a
real, non-vacuous check: it directly targets the exact defect (site 13/14
used to return `is_ok=true` UNCONDITIONALLY, ignoring `leaf` entirely) and the
lane's sabotage step (reverting the guard) flips it RED regardless of which
host is running.

## Scenarios

### GPU backend / session adapter honesty (A3, sites 11-20)

#### site 11 — WebGpuBackend.init() honesty

#### init()'s return value equals gpu_ready, never a bare true

- init()'s return value equals gpu_ready, never a bare true
   - Expected: ok equals `backend.gpu_ready`
   - Expected: backend.initialized equals `backend.gpu_ready`
   - Expected: ok is false
   - Expected: pixels.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("init()'s return value equals gpu_ready, never a bare true")
var backend = WebGpuBackend.create()
val ok = backend.init(4, 4)
expect(ok).to_equal(backend.gpu_ready)
expect(backend.initialized).to_equal(backend.gpu_ready)
# This host has no real WebGPU adapter (no browser host, weak
# runtime stubs) — the honest result is false, not a fabricated
# true.
expect(ok).to_equal(false)
# The CPU-mirror draw path must still work (M7 parity floor) even
# though `initialized` now honestly tracks GPU readiness, not
# "was init() called".
backend.clear(0xFF202020u32)
backend.draw_text(0, 0, "A", 0xFFFFFFFFu32, 7)
val pixels = backend.read_pixels()
expect(pixels.len()).to_equal(16)
backend.shutdown()
```

</details>

#### probe_backend(\

- probe_backend(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_backend(\")
val probe = Engine2D.probe_backend(4, 4, "webgpu")
expect(backend_status_text(probe.status)).to_not_equal("Initialized")
```

</details>

#### sites 13/14 — Vulkan ICD device creation is gated on the real probe

#### create_instance.is_ok is gated on leaf, not unconditional

- create_instance.is_ok is gated on leaf, not unconditional
   - Expected: result.is_ok equals `leaf == "leaf=dlopen"`
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_instance.is_ok is gated on leaf, not unconditional")
val result = vk_icd_create_instance()
val leaf = vk_icd_probe_leaf()
expect(result.is_ok).to_equal(leaf == "leaf=dlopen")
val leaf_ok = result.leaf == "dlopen" or result.leaf == "structured"
expect(leaf_ok).to_equal(true)
```

</details>

#### create_device.is_ok is gated on leaf, not unconditional

- create_device.is_ok is gated on leaf, not unconditional
   - Expected: dev.is_ok equals `leaf == "leaf=dlopen"`
   - Expected: inst.is_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_device.is_ok is gated on leaf, not unconditional")
val inst = vk_icd_create_instance()
if inst.is_ok:
    val dev = vk_icd_create_device(inst.instance_handle)
    val leaf = vk_icd_probe_leaf()
    expect(dev.is_ok).to_equal(leaf == "leaf=dlopen")
else:
    # No real instance to build a device on top of — the honest
    # answer is refusal, not a fabricated device.
    expect(inst.is_ok).to_equal(false)
```

</details>

#### dxvk d3d11 device probe never fabricates when its ICD dependency refuses

- dxvk d3d11 device probe never fabricates when its ICD dependency refuses
   - Expected: probe.is_ok equals `leaf == "leaf=dlopen"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dxvk d3d11 device probe never fabricates when its ICD dependency refuses")
val probe = dxvk_d3d11_probe_device()
val leaf = vk_icd_probe_leaf()
expect(probe.is_ok).to_equal(leaf == "leaf=dlopen")
```

</details>

#### sites 15-19 — session adapter readback() never claims success with zero pixels moved

#### metal adapter readback() refuses (not-initialized live, initialized-path static)

- metal adapter readback() refuses (not-initialized live, initialized-path static)
   - Expected: r.len() > 0 is true
   - Expected: readback_still_ends_in_bare_success_sentinel(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("metal adapter readback() refuses (not-initialized live, initialized-path static)")
# Live half: an un-initialized adapter must refuse, not crash.
var a = BackendMetalAdapter.create("test")
val r = a.readback(0, 0, 4, 4)
expect(r.len() > 0).to_equal(true)
# Static half: init_device() calls a real `rt_metal_create_device`
# extern this interpreter test runner cannot resolve on this host
# ("unknown extern function"/arity mismatch), so the
# initialized+valid-dims path cannot be reached live here — verify
# by anchored source shape instead (see helper docstring above).
val path = "src/lib/gc_async_mut/gpu/session/backend_metal_adapter.spl"
expect(readback_still_ends_in_bare_success_sentinel(path)).to_equal(false)
```

</details>

#### webgpu adapter readback() refuses (not-initialized live, initialized-path static)

- webgpu adapter readback() refuses (not-initialized live, initialized-path static)
   - Expected: r.len() > 0 is true
   - Expected: readback_still_ends_in_bare_success_sentinel(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("webgpu adapter readback() refuses (not-initialized live, initialized-path static)")
var a = BackendWebgpuAdapter.create("test")
val r = a.readback(0, 0, 4, 4)
expect(r.len() > 0).to_equal(true)
val path = "src/lib/gc_async_mut/gpu/session/backend_webgpu_adapter.spl"
expect(readback_still_ends_in_bare_success_sentinel(path)).to_equal(false)
```

</details>

#### vulkan adapter readback() refuses (not-initialized live, initialized-path static)

- vulkan adapter readback() refuses (not-initialized live, initialized-path static)
   - Expected: r.len() > 0 is true
   - Expected: readback_still_ends_in_bare_success_sentinel(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("vulkan adapter readback() refuses (not-initialized live, initialized-path static)")
var a = BackendVulkanAdapter.create("test")
val r = a.readback(0, 0, 4, 4)
expect(r.len() > 0).to_equal(true)
val path = "src/lib/gc_async_mut/gpu/session/backend_vulkan_adapter.spl"
expect(readback_still_ends_in_bare_success_sentinel(path)).to_equal(false)
```

</details>

#### cuda adapter readback() refuses (not-initialized live, initialized-path static)

- cuda adapter readback() refuses (not-initialized live, initialized-path static)
   - Expected: r.len() > 0 is true
   - Expected: readback_still_ends_in_bare_success_sentinel(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cuda adapter readback() refuses (not-initialized live, initialized-path static)")
var a = BackendCudaAdapter.create("test")
val r = a.readback(0, 0, 4, 4)
expect(r.len() > 0).to_equal(true)
val path = "src/lib/gc_async_mut/gpu/session/backend_cuda_adapter.spl"
expect(readback_still_ends_in_bare_success_sentinel(path)).to_equal(false)
```

</details>

#### cpu adapter readback() refuses (no real pixel buffer to copy)

- cpu adapter readback() refuses (no real pixel buffer to copy)
   - Expected: r.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cpu adapter readback() refuses (no real pixel buffer to copy)")
var a = BackendCpuAdapter.create("test")
a.init_device()
val r = a.readback(0, 0, 4, 4)
expect(r.len() > 0).to_equal(true)
```

</details>

#### site 20 — metal adapter supports_*() is platform- and device-gated

#### supports_compute() is false on this host

- supports_compute() is false on this host
   - Expected: a.supports_compute() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports_compute() is false on this host")
var a = BackendMetalAdapter.create("test")
expect(a.supports_compute()).to_equal(false)
```

</details>

#### supports_graphics() and supports_present() are false on this host

- supports_graphics() and supports_present() are false on this host
   - Expected: a.supports_graphics() is false
   - Expected: a.supports_present() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports_graphics() and supports_present() are false on this host")
var a = BackendMetalAdapter.create("test")
expect(a.supports_graphics()).to_equal(false)
expect(a.supports_present()).to_equal(false)
```

</details>

#### engine.spl mitigation unification — default and viable detection agree

#### a real cpu_mirror-only backend is rejected by both detect_best_backend() and detect_best_backend_viable()

- a real cpu_mirror-only backend is rejected by both detect_best_backend() and detect_best_backend_viable()
   - Expected: rb.source equals `cpu_mirror`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a real cpu_mirror-only backend is rejected by both detect_best_backend() and detect_best_backend_viable()")
var stub = WebGpuBackend.create()
stub.init(8, 8)
val rb = stub.read_pixels_with_source()
expect(rb.source).to_equal("cpu_mirror")
stub.shutdown()

val viable_probe = Engine2D.probe_backend_viable("webgpu")
expect(backend_status_text(viable_probe.status)).to_not_equal("Initialized")
expect(Engine2D.detect_best_backend()).to_not_equal("webgpu")
expect(Engine2D.detect_best_backend_viable()).to_not_equal("webgpu")
```

</details>

#### detect_best_backend() never returns a backend that fails the deep viability probe

- detect_best_backend() never returns a backend that fails the deep viability probe
   - Expected: backend_status_text(selected_viable.status) equals `Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detect_best_backend() never returns a backend that fails the deep viability probe")
# The generic form of the same defect: on THIS host, webgpu's own
# init() (site 11, now fixed) already fails the SHALLOW probe, so
# a webgpu-only check can't distinguish "the default path applies
# the deep check" from "the default path never even shallow-
# passed webgpu" — it would stay green even if the mitigation
# unification were reverted. This invariant is defect-shaped
# instead of backend-name-shaped: whichever candidate
# detect_best_backend() lands on, probe_backend_viable() on that
# SAME name must also report Initialized (the "directx falls back
# to directx-software-emulation" candidate is exactly the kind of
# shallow-pass/deep-fail case this catches on this host).
val selected = Engine2D.detect_best_backend()
val selected_viable = Engine2D.probe_backend_viable(selected)
expect(backend_status_text(selected_viable.status)).to_equal("Initialized")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WM-HOST-PLATFORM-003`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f2befdea037217370bb4b5de40d30a9034f94a43e3f95e2a975d0aaabaa825e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f2befdea037217370bb4b5de40d30a9034f94a43e3f95e2a975d0aaabaa825e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f2befdea037217370bb4b5de40d30a9034f94a43e3f95e2a975d0aaabaa825e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'init()'s return value equals gpu_ready, never a bare true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_backend(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_instance.is_ok is gated on leaf, not unconditional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
