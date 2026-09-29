# web_gpu_first_present_decision_spec

> Simple Web gpu-first present lane — honest per-frame offload decision

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_gpu_first_present_decision_spec

Simple Web gpu-first present lane — honest per-frame offload decision

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Web gpu-first present lane — honest per-frame offload decision

@tag: rendering, web, gpu, offload, presenter, provenance
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl 90%

The default (SIMPLE_WEB_GPU_PAINT unset) present path attempts GPU offload
first and reports what actually happened through a per-frame decision string
(`simple_web_layout_render_html_gpu_first_decision`). This spec discriminates
the honesty claims, not just a pass:

- a degenerate surface is "not-requested", never a fabricated offload;
- an explicit CPU backend is a request (cpu-raster), with the exact verdict
  reason embedded — never a silent software default;
- an unknown backend is a visible decline with its verdict reason;
- on a GPU-candidate backend the decision must either carry device provenance
  (`source=device_readback`) for any offload claim, or state a concrete
  decline reason — a GPU label without device provenance is a hard failure
  (see doc/08_tracking/bug/web_render_gpu_backend_provenance_fabricated_2026-06-17.md).

## Scenarios

### gpu-first present decision honesty

#### reports a degenerate surface as not-requested instead of claiming offload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a degenerate surface as not-requested instead of claiming offload
- Arm the render budget floor so interpreter load cannot truncate styles
- Request a 0x0 present through the gpu-first lane
   - Expected: decision equals `gpu-first:not-requested:degenerate-surface`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a degenerate surface as not-requested instead of claiming offload")
step("Arm the render budget floor so interpreter load cannot truncate styles")
simple_web_layout_set_render_budget_floor_ms(900000)

step("Request a 0x0 present through the gpu-first lane")
val decision = simple_web_layout_render_html_gpu_first_decision(FILL_HTML, 0, 0, "vulkan")
expect(decision).to_equal("gpu-first:not-requested:degenerate-surface")
```

</details>

#### treats an explicit CPU backend as a cpu-raster request carrying the exact verdict reason

- treats an explicit CPU backend as a cpu-raster request carrying the exact verdict reason
- Confirm the backend verdict the decision must embed
   - Expected: web_gpu_paint_backend_verdict("software") equals `cpu-backend-not-gpu-offload`
- Present on the software backend and read the decision


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats an explicit CPU backend as a cpu-raster request carrying the exact verdict reason")
simple_web_layout_set_render_budget_floor_ms(900000)

step("Confirm the backend verdict the decision must embed")
expect(web_gpu_paint_backend_verdict("software")).to_equal("cpu-backend-not-gpu-offload")

step("Present on the software backend and read the decision")
val decision = simple_web_layout_render_html_gpu_first_decision(FILL_HTML, SURFACE_W, SURFACE_H, "software")
expect(decision).to_contain("gpu-first:cpu-raster:offloaded=none:cpu=full-frame")
expect(decision).to_contain("reason=cpu-backend-not-gpu-offload")
```

</details>

#### declines an unknown backend visibly with its verdict reason, never silently

- declines an unknown backend visibly with its verdict reason, never silently
- Confirm the unknown-backend verdict
   - Expected: web_gpu_paint_backend_verdict("quantum9") equals `unknown-backend-not-gpu-offload`
- Present on the unknown backend and read the decision


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("declines an unknown backend visibly with its verdict reason, never silently")
simple_web_layout_set_render_budget_floor_ms(900000)

step("Confirm the unknown-backend verdict")
expect(web_gpu_paint_backend_verdict("quantum9")).to_equal("unknown-backend-not-gpu-offload")

step("Present on the unknown backend and read the decision")
val decision = simple_web_layout_render_html_gpu_first_decision(FILL_HTML, SURFACE_W, SURFACE_H, "quantum9")
expect(decision).to_contain("gpu-first:cpu-raster:offloaded=none")
expect(decision).to_contain("reason=unknown-backend-not-gpu-offload")
```

</details>

#### on a GPU-candidate backend either proves device provenance or states a concrete decline reason

- on a GPU-candidate backend either proves device provenance or states a concrete decline reason
- Resolve the real backend through the capability probe
- Run the gpu-first lane against the vulkan candidate request
- An offload claim must carry device readback provenance
- A decline must state a concrete reason — never a silent CPU fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("on a GPU-candidate backend either proves device provenance or states a concrete decline reason")
simple_web_layout_set_render_budget_floor_ms(900000)

step("Resolve the real backend through the capability probe")
val resolved = simple_web_engine2d_resolved_backend_name(SURFACE_W, SURFACE_H, "vulkan")
# Fail-closed lane selection: the probe answers vulkan (device up) or
# software (probe failed); anything else is a hard failure.
expect(resolved == "vulkan" or resolved == "software").to_be(true)

step("Run the gpu-first lane against the vulkan candidate request")
val decision = simple_web_layout_render_html_gpu_first_decision(FILL_HTML, SURFACE_W, SURFACE_H, "vulkan")
expect(decision).to_contain("gpu-first:")
if decision.contains(":offloaded=rect_fill:"):
    step("An offload claim must carry device readback provenance")
    expect(decision).to_contain("source=device_readback")
    expect(decision).to_contain(":device_identity=")
else:
    step("A decline must state a concrete reason — never a silent CPU fallback")
    expect(decision).to_contain("reason=")
```

</details>

#### never labels a frame gpu-* unless the readback proves a device produced it

- never labels a frame gpu-* unless the readback proves a device produced it
- Sweep every gpu-paint-candidate backend, present and unavailable alike
- Any gpu-* label must carry device readback provenance
- A CPU-sourced readback must never be labelled gpu-* nor claim an offload
- The sweep must have asserted something — a run where no backend matched either arm proves nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never labels a frame gpu-* unless the readback proves a device produced it")
simple_web_layout_set_render_budget_floor_ms(900000)

step("Sweep every gpu-paint-candidate backend, present and unavailable alike")
# The offload label used to be derived from `economics.residual_pixels` —
# a prediction made BEFORE dispatch — so a backend that returned Ok but
# presented on the CPU was still labelled `gpu-full` while its own
# `source=` field said `cpu_mirror`. The label and the readback are one
# claim and must agree.
val names = ["vulkan", "metal", "cuda", "opencl", "webgpu", "rocm"]
var i = 0
# Anti-vacuity counter. Both arms below are conditional, so a sweep in
# which no decision matched EITHER arm would assert nothing at all and
# still pass — the same silent-skip shape fixed in
# web_engine2d_gpu_offload_parity_spec. Count the backends that actually
# exercised an arm and require at least one, matching the `declines`
# guard already used in web_gpu_present_paint_coverage_spec.
var examined = 0
while i < names.len():
    val name = names[i]
    val decision = simple_web_layout_render_html_gpu_first_decision(
        FILL_HTML, SURFACE_W, SURFACE_H, name)
    val claims_gpu = (decision.contains("gpu-first:gpu-full")
        or decision.contains("gpu-first:gpu-partial"))

    step("Any gpu-* label must carry device readback provenance")
    if claims_gpu:
        expect(decision).to_contain("source=device_readback")
        expect(decision).to_contain(":offloaded=rect_fill:")
        examined = examined + 1

    step("A CPU-sourced readback must never be labelled gpu-* nor claim an offload")
    if decision.contains("source=cpu_mirror") or decision.contains("source=cpu_fallback"):
        expect(claims_gpu).to_be(false)
        expect(decision).to_contain(":offloaded=none")
        examined = examined + 1
    i = i + 1
print "[gpu-first-decision] label-vs-readback sweep: {examined} of {names.len()} backends exercised an assertion arm"
step("The sweep must have asserted something — a run where no backend matched either arm proves nothing")
expect(examined).to_be_greater_than(0)
```

</details>

#### never reports gpu_backend_used unless the dispatch readback proves a device

- never reports gpu_backend_used unless the dispatch readback proves a device
- Sweep every gpu-paint-candidate backend plus an explicit CPU backend
- A GPU claim must be backed by a device_readback source
- A CPU-sourced readback must never claim the GPU was used
- The sweep must have inspected a real receipt — all-empty receipts prove nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never reports gpu_backend_used unless the dispatch readback proves a device")
simple_web_layout_set_render_budget_floor_ms(900000)

step("Sweep every gpu-paint-candidate backend plus an explicit CPU backend")
# The `[web-gpu-paint]` dispatch marker derived `gpu_backend_used` from
# `_backend_is_cpu(readback.source)` — a backend-NAME classifier fed a
# readback-SOURCE string. No source ("device_readback", "cpu_mirror",
# "cpu_fallback", ...) is ever in that classifier's vocabulary, so the
# flag was a constant `true`: `webgpu` and even `cpu_simd` reported
# `gpu_backend_used=true` beside their own `readback_source=cpu_mirror`.
# The claim and the readback are one claim and must agree.
val names = ["vulkan", "metal", "cuda", "opencl", "webgpu", "rocm", "cpu_simd"]
var i = 0
# Anti-vacuity counter: if EVERY backend returned an empty receipt this
# example would pass having asserted nothing and printed nothing. At
# least one backend must reach dispatch for the sweep to mean anything.
var dispatched = 0
while i < names.len():
    val name = names[i]
    web_gpu_paint_last_dispatch_receipt_reset()
    simple_web_layout_render_html_gpu_first_decision(
        FILL_HTML, SURFACE_W, SURFACE_H, name)
    val receipt = web_gpu_paint_last_dispatch_receipt()
    # An empty receipt means the backend never reached dispatch
    # (Engine2D declined to construct); nothing to assert for it.
    if receipt != "":
        dispatched = dispatched + 1
        step("A GPU claim must be backed by a device_readback source")
        if receipt.contains("gpu_backend_used=true"):
            expect(receipt).to_contain("readback_source=device_readback")

        step("A CPU-sourced readback must never claim the GPU was used")
        if (receipt.contains("readback_source=cpu_mirror")
            or receipt.contains("readback_source=cpu_fallback")):
            expect(receipt).to_contain("gpu_backend_used=false")
    i = i + 1
print "[gpu-first-decision] dispatch-receipt sweep: {dispatched} of {names.len()} backends reached dispatch"
step("The sweep must have inspected a real receipt — all-empty receipts prove nothing")
expect(dispatched).to_be_greater_than(0)
```

</details>

#### maps the SIMPLE_WEB_GPU_PAINT routing env to exactly one of the three modes

- maps the SIMPLE_WEB_GPU_PAINT routing env to exactly one of the three modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps the SIMPLE_WEB_GPU_PAINT routing env to exactly one of the three modes")
val mode = web_gpu_paint_mode()
expect(mode == "off" or mode == "measured" or mode == "gpu-first").to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `721f2c5f22aa4b1c9fdee6159ca058ac79782c9cd1f1c250cea542b8bfab1666`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `721f2c5f22aa4b1c9fdee6159ca058ac79782c9cd1f1c250cea542b8bfab1666`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `721f2c5f22aa4b1c9fdee6159ca058ac79782c9cd1f1c250cea542b8bfab1666`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a degenerate surface as not-requested instead of claiming offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats an explicit CPU backend as a cpu-raster request carrying the exact verdict reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declines an unknown backend visibly with its verdict reason, never silently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
