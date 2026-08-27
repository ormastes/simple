# Backend Alias Browser Specification

> Tests covering Browser backend aliases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Alias Browser Specification

## Scenarios

### Browser backend aliases

#### preserves native and accelerated backend names through the browser adapter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves native and accelerated backend names through the browser adapter
   - Expected: BrowserBackend.create(64, 48, "metal").unwrap().gpu_backend() equals `metal`
   - Expected: BrowserBackend.create(64, 48, "cuda").unwrap().gpu_backend() equals `cuda`
   - Expected: BrowserBackend.create(64, 48, "hip").unwrap().gpu_backend() equals `rocm`
   - Expected: BrowserBackend.create(64, 48, "vulkan").unwrap().gpu_backend() equals `vulkan`
   - Expected: BrowserBackend.create(64, 48, "opencl").unwrap().gpu_backend() equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves native and accelerated backend names through the browser adapter")
expect(BrowserBackend.create(64, 48, "metal").unwrap().gpu_backend()).to_equal("metal")
expect(BrowserBackend.create(64, 48, "cuda").unwrap().gpu_backend()).to_equal("cuda")
expect(BrowserBackend.create(64, 48, "hip").unwrap().gpu_backend()).to_equal("rocm")
expect(BrowserBackend.create(64, 48, "vulkan").unwrap().gpu_backend()).to_equal("vulkan")
expect(BrowserBackend.create(64, 48, "opencl").unwrap().gpu_backend()).to_equal("opencl")
```

</details>

#### preserves DirectX aliases as the DirectX backend lane

- preserves DirectX aliases as the DirectX backend lane
   - Expected: BrowserBackend.create(64, 48, "directx").unwrap().gpu_backend() equals `directx`
   - Expected: BrowserBackend.create(64, 48, "dx11").unwrap().gpu_backend() equals `directx`
   - Expected: BrowserBackend.create(64, 48, "d3d11").unwrap().gpu_backend() equals `directx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves DirectX aliases as the DirectX backend lane")
expect(BrowserBackend.create(64, 48, "directx").unwrap().gpu_backend()).to_equal("directx")
expect(BrowserBackend.create(64, 48, "dx11").unwrap().gpu_backend()).to_equal("directx")
expect(BrowserBackend.create(64, 48, "d3d11").unwrap().gpu_backend()).to_equal("directx")
```

</details>

#### preserves CPU SIMD aliases through the browser adapter

- preserves CPU SIMD aliases through the browser adapter
   - Expected: BrowserBackend.create(64, 48, "simd_cpu").unwrap().gpu_backend() equals `cpu_simd`
   - Expected: BrowserBackend.create(64, 48, "cpu-simd").unwrap().gpu_backend() equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves CPU SIMD aliases through the browser adapter")
expect(BrowserBackend.create(64, 48, "simd_cpu").unwrap().gpu_backend()).to_equal("cpu_simd")
expect(BrowserBackend.create(64, 48, "cpu-simd").unwrap().gpu_backend()).to_equal("cpu_simd")
```

</details>

#### uses the resolved auto backend for repeated pure Simple render frames

- uses the resolved auto backend for repeated pure Simple render frames
   - Expected: resolved equals `web_render_resolved_engine2d_backend_name(1, 1, "auto")`
   - Expected: backend.gpu_backend() equals `resolved`
   - Expected: backend.last_artifact_engine2d_backend equals `resolved`
   - Expected: backend.gpu_backend() equals `resolved`
   - Expected: backend.last_artifact_engine2d_backend equals `resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the resolved auto backend for repeated pure Simple render frames")
val state = _backend_alias_browser_state()
val backend = BrowserBackend.create(64, 48, "auto").unwrap()
val resolved = backend.gpu_backend()

expect(resolved.len()).to_be_greater_than(0)
expect(resolved).to_not_equal("auto")
expect(resolved).to_equal(web_render_resolved_engine2d_backend_name(1, 1, "auto"))

backend.render_frame(state.tree, state)
expect(backend.gpu_backend()).to_equal(resolved)
expect(backend.last_artifact_engine2d_backend).to_equal(resolved)

backend.resize(80, 48)
backend.render_frame(state.tree, state)
expect(backend.gpu_backend()).to_equal(resolved)
expect(backend.last_artifact_engine2d_backend).to_equal(resolved)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_alias_browser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser backend aliases.
- Browser backend aliases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `185c8e52930a186af937f2764f63834774f7d5a75726a58b3fb17b57d5aa02ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `185c8e52930a186af937f2764f63834774f7d5a75726a58b3fb17b57d5aa02ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `185c8e52930a186af937f2764f63834774f7d5a75726a58b3fb17b57d5aa02ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ui/backend_alias_browser_spec.spl
mirror: doc/06_spec/01_unit/app/ui/backend_alias_browser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/backend_alias_browser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/backend_alias_browser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/backend_alias_browser_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves native and accelerated backend names through the browser adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/backend_alias_browser_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves DirectX aliases as the DirectX backend lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/backend_alias_browser_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves CPU SIMD aliases through the browser adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
