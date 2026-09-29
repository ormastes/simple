# Engine2d Backend Matrix Specification

> Tests covering Engine2D backend matrix — host detection, Engine2D backend matrix — alias canonicalization, Engine2D backend matrix — per-backend coherence, Engine2D backend matrix — guaranteed CPU lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Backend Matrix Specification

## Scenarios

### Engine2D backend matrix — host detection

#### detect_best_backend returns a canonical name from the renderer priority order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detect_best_backend returns a canonical name from the renderer priority order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detect_best_backend returns a canonical name from the renderer priority order")
val best = Engine2D.detect_best_backend()
print("detected best backend: {best}")
assert_true(best.len() > 0)
val canon = backend_canonical_name(best)
assert_true(contains_name(renderer_priority_order(), canon))
```

</details>

#### list_backends is non-empty and always contains the cpu scalar fallback

- list_backends is non-empty and always contains the cpu scalar fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("list_backends is non-empty and always contains the cpu scalar fallback")
val avail = Engine2D.list_backends()
assert_true(avail.len() > 0)
assert_true(contains_name(avail, "cpu"))
```

</details>

#### every listed backend name is already canonical

- every listed backend name is already canonical


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("every listed backend name is already canonical")
val avail = Engine2D.list_backends()
val n = avail.len()
var i = 0
var all_canonical = true
while i < n:
    val name = avail[i]
    if backend_canonical_name(name) != name:
        print("non-canonical listed backend: {name}")
        all_canonical = false
    i = i + 1
assert_true(all_canonical)
```

</details>

### Engine2D backend matrix — alias canonicalization

#### directx family aliases canonicalize to directx

- directx family aliases canonicalize to directx
   - Expected: backend_canonical_name("d3d11") equals `directx`
   - Expected: backend_canonical_name("d3d12") equals `directx`
   - Expected: backend_canonical_name("dx11") equals `directx`
   - Expected: backend_canonical_name("dx12") equals `directx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("directx family aliases canonicalize to directx")
expect(backend_canonical_name("d3d11")).to_equal("directx")
expect(backend_canonical_name("d3d12")).to_equal("directx")
expect(backend_canonical_name("dx11")).to_equal("directx")
expect(backend_canonical_name("dx12")).to_equal("directx")
```

</details>

#### cpu-simd family aliases canonicalize to cpu_simd

- cpu-simd family aliases canonicalize to cpu_simd
   - Expected: backend_canonical_name("cpu-simd") equals `cpu_simd`
   - Expected: backend_canonical_name("simd_cpu") equals `cpu_simd`
   - Expected: backend_canonical_name("simd-cpu") equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu-simd family aliases canonicalize to cpu_simd")
expect(backend_canonical_name("cpu-simd")).to_equal("cpu_simd")
expect(backend_canonical_name("simd_cpu")).to_equal("cpu_simd")
expect(backend_canonical_name("simd-cpu")).to_equal("cpu_simd")
```

</details>

<details>
<summary>Advanced: canonical matrix names map to themselves</summary>

#### canonical matrix names map to themselves

- canonical matrix names map to themselves
   - Expected: backend_canonical_name("metal") equals `metal`
   - Expected: backend_canonical_name("vulkan") equals `vulkan`
   - Expected: backend_canonical_name("directx") equals `directx`
   - Expected: backend_canonical_name("cpu_simd") equals `cpu_simd`
   - Expected: backend_canonical_name("software") equals `software`
   - Expected: backend_canonical_name("cpu") equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("canonical matrix names map to themselves")
expect(backend_canonical_name("metal")).to_equal("metal")
expect(backend_canonical_name("vulkan")).to_equal("vulkan")
expect(backend_canonical_name("directx")).to_equal("directx")
expect(backend_canonical_name("cpu_simd")).to_equal("cpu_simd")
expect(backend_canonical_name("software")).to_equal("software")
expect(backend_canonical_name("cpu")).to_equal("cpu")
```

</details>


</details>

### Engine2D backend matrix — per-backend coherence

#### metal initializes+renders or is coherently unavailable

- metal initializes+renders or is coherently unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("metal initializes+renders or is coherently unavailable")
assert_true(matrix_entry_coherent("metal"))
```

</details>

#### vulkan initializes+renders or is coherently unavailable

- vulkan initializes+renders or is coherently unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vulkan initializes+renders or is coherently unavailable")
assert_true(matrix_entry_coherent("vulkan"))
```

</details>

#### directx initializes+renders or is coherently unavailable

- directx initializes+renders or is coherently unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("directx initializes+renders or is coherently unavailable")
assert_true(matrix_entry_coherent("directx"))
```

</details>

#### cpu_simd initializes+renders or is coherently unavailable

- cpu_simd initializes+renders or is coherently unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu_simd initializes+renders or is coherently unavailable")
assert_true(matrix_entry_coherent("cpu_simd"))
```

</details>

#### software initializes+renders or is coherently unavailable

- software initializes+renders or is coherently unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("software initializes+renders or is coherently unavailable")
assert_true(matrix_entry_coherent("software"))
```

</details>

#### cpu initializes+renders or is coherently unavailable

- cpu initializes+renders or is coherently unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu initializes+renders or is coherently unavailable")
assert_true(matrix_entry_coherent("cpu"))
```

</details>

#### reports the macOS Metal gate without emulation on non-macOS hosts

- reports the macOS Metal gate without emulation on non-macOS hosts
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.feature_gate equals `macos`
   - Expected: created.is_ok() is false
   - Expected: failure.selected_name == "cpu" or failure.selected_name == "software" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports the macOS Metal gate without emulation on non-macOS hosts")
# Deterministic platform gate, not a device race: on a non-macOS host
# metal is ALWAYS Unavailable behind the "macos" feature gate, and the
# strict create must never quietly substitute a software raster for it.
if not is_macos():
    val probe = Engine2D.probe_backend(4, 4, "metal")
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    expect(probe.feature_gate).to_equal("macos")
    val created = Engine2D.create_with_backend_strict(16, 16, "metal")
    expect(created.is_ok()).to_equal(false)
    if not created.is_ok():
        val failure = created.unwrap_err()
        expect(failure.selected_name == "cpu" or failure.selected_name == "software").to_equal(false)
```

</details>

### Engine2D backend matrix — guaranteed CPU lanes

#### cpu strict-create + fill + readback works on any host

- cpu strict-create + fill + readback works on any host


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu strict-create + fill + readback works on any host")
assert_true(strict_render_ok("cpu"))
```

</details>

#### software strict-create + fill + readback works on any host

- software strict-create + fill + readback works on any host


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("software strict-create + fill + readback works on any host")
# Was gated on `probe_backend("software").status == Initialized` — a
# prediction about a SECOND, independent create, so a probe hiccup used
# to skip the whole lane and still print a pass. software is a pure
# scalar rasterizer that owes no device, so the create is attempted
# unconditionally and is REQUIRED to succeed and to be pixel-correct.
# Verified still true at `ulimit -n 44` across 3/3 runs.
assert_true(strict_render_ok("software"))
```

</details>

#### closes with an explicit reading rule for this run's GPU evidence

- closes with an explicit reading rule for this run's GPU evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("closes with an explicit reading rule for this run's GPU evidence")
print("[probe-gpu] RUN VERDICT: this run's GPU evidence is exactly the set of '[probe-gpu] <backend>: GPU-PROVEN' lines above.")
print("[probe-gpu] RUN VERDICT: every '[probe-gpu] <backend>: GPU BRANCH SKIPPED' line marks a backend that proves NOTHING about the GPU path.")
print("[probe-gpu] RUN VERDICT: a PASS with no GPU-PROVEN line does NOT attest any GPU backend — read it as 'device unavailable', not as 'the GPU matrix works'.")
print("[probe-gpu] RUN VERDICT: every '[toctou]' line above marks a place where an independent probe and the independent create disagreed; the create is what was asserted on.")
assert_true(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/02_integration/gpu/engine2d_backend_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D backend matrix — host detection, Engine2D backend matrix — alias canonicalization, Engine2D backend matrix — per-backend coherence, Engine2D backend matrix — guaranteed CPU lanes.
- Engine2D backend matrix — host detection
- Engine2D backend matrix — alias canonicalization
- Engine2D backend matrix — per-backend coherence
- Engine2D backend matrix — guaranteed CPU lanes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `584afae7c5b87207e951a7b029a8b69bc7e6c0037607d740509750a43ee591f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `584afae7c5b87207e951a7b029a8b69bc7e6c0037607d740509750a43ee591f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `584afae7c5b87207e951a7b029a8b69bc7e6c0037607d740509750a43ee591f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/gpu/engine2d_backend_matrix_spec.spl
mirror: doc/06_spec/02_integration/gpu/engine2d_backend_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/gpu/engine2d_backend_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/gpu/engine2d_backend_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/gpu/engine2d_backend_matrix_spec.spl:309:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detect_best_backend returns a canonical name from the renderer priority order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu/engine2d_backend_matrix_spec.spl:318:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'list_backends is non-empty and always contains the cpu scalar fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu/engine2d_backend_matrix_spec.spl:325:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every listed backend name is already canonical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
