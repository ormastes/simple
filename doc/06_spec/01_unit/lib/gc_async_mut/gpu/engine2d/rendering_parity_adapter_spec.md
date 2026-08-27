# Rendering Parity Adapter Specification

> Tests covering Engine2D rendering parity adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rendering Parity Adapter Specification

## Scenarios

### Engine2D rendering parity adapter

#### maps manifest row names to explicit Engine2D backends

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps manifest row names to explicit Engine2D backends
   - Expected: engine2d_rendering_parity_backend_name("simple_cpu", "").unwrap() equals `cpu`
   - Expected: engine2d_rendering_parity_backend_name("simple_simd", "").unwrap() equals `cpu_simd`
   - Expected: engine2d_rendering_parity_backend_name("simple_gpu", "vulkan").unwrap() equals `vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps manifest row names to explicit Engine2D backends")
expect(engine2d_rendering_parity_backend_name("simple_cpu", "").unwrap()).to_equal("cpu")
expect(engine2d_rendering_parity_backend_name("simple_simd", "").unwrap()).to_equal("cpu_simd")
expect(engine2d_rendering_parity_backend_name("simple_gpu", "vulkan").unwrap()).to_equal("vulkan")
expect(engine2d_rendering_parity_backend_name("simple_gpu", "cpu").is_err()).to_be(true)
```

</details>

#### converts ARGB words to tightly packed straight RGBA bytes

- converts ARGB words to tightly packed straight RGBA bytes
   - Expected: ENGINE2D_PARITY_CONVERTER equals `engine2d-argb32-to-rgba8-v1`
   - Expected: output.rgba equals `[0x12u8, 0x34u8, 0x56u8, 0x80u8, 0xABu8, 0xCDu8, 0xEFu8, 0xFFu8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts ARGB words to tightly packed straight RGBA bytes")
val readback = engine2d_readback([0x80123456u32, 0xFFABCDEFu32], "cpu_mirror")
val output = engine2d_rendering_parity_canonicalize(readback, 2, 1, "cpu", "cpu")
expect(ENGINE2D_PARITY_CONVERTER).to_equal("engine2d-argb32-to-rgba8-v1")
expect(output.valid).to_be(true)
expect(output.rgba).to_equal([0x12u8, 0x34u8, 0x56u8, 0x80u8, 0xABu8, 0xCDu8, 0xEFu8, 0xFFu8])
```

</details>

#### rejects fallback and forged GPU provenance

- rejects fallback and forged GPU provenance
   - Expected: fallback.reason equals `backend-fallback`
   - Expected: forged.reason equals `device-identity-required`
   - Expected: evidence.status equals `fail`
   - Expected: pass_evidence.status equals `pass`
   - Expected: pass_evidence.execution_id equals `run-proven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects fallback and forged GPU provenance")
val cpu = engine2d_readback([0xFFFFFFFFu32], "cpu_mirror")
val fallback = engine2d_rendering_parity_canonicalize(cpu, 1, 1, "vulkan", "cpu")
expect(fallback.valid).to_be(false)
expect(fallback.reason).to_equal("backend-fallback")

val zero_identity = engine2d_readback_with_identity([0xFFFFFFFFu32], "device_readback", 41, 0)
val forged = engine2d_rendering_parity_canonicalize(zero_identity, 1, 1, "vulkan", "vulkan")
expect(forged.valid).to_be(false)
expect(forged.reason).to_equal("device-identity-required")
val evidence = engine2d_rendering_parity_evidence("forged", zero_identity, 1, 1, "vulkan", "vulkan", "run-forged", "revision", 1, 0, false, "", 1, 1).unwrap()
expect(evidence.status).to_equal("fail")
expect(evidence.physical_backend).to_be(true)

val proven = engine2d_readback_with_identity([0xFFFFFFFFu32], "device_readback", 41, 73)
val pass_evidence = engine2d_rendering_parity_evidence("proven", proven, 1, 1, "vulkan", "vulkan", "run-proven", "revision", 1, 0, false, "", 1, 1).unwrap()
expect(pass_evidence.status).to_equal("pass")
expect(pass_evidence.execution_id).to_equal("run-proven")
```

</details>

#### rejects malformed length and checksum evidence

- rejects malformed length and checksum evidence
   - Expected: malformed.reason equals `invalid-pixel-count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed length and checksum evidence")
val short = engine2d_readback([0xFFFFFFFFu32], "cpu_mirror")
val malformed = engine2d_rendering_parity_canonicalize(short, 2, 1, "cpu_simd", "cpu_simd")
expect(malformed.valid).to_be(false)
expect(malformed.reason).to_equal("invalid-pixel-count")
```

</details>

#### executes one observed composition independently without rerendering HTML

- executes one observed composition independently without rerendering HTML
   - Expected: cpu.evidence.execution_id equals `execution-cpu`
   - Expected: cpu.evidence.requested_backend equals `cpu`
   - Expected: cpu.output.stages[3].output_checksum equals `cpu_stages[3].output_checksum`
   - Expected: simd.evidence.execution_id equals `execution-cpu-simd`
   - Expected: simd.evidence.simd_execution_receipt equals `simd-hit-1`
   - Expected: simd.output.rgba8 equals `cpu.output.rgba8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes one observed composition independently without rerendering HTML")
val html = "<style>body{margin:0;background:#102030}#box{width:8px;height:8px;background:#abcdef}</style><div id='box'></div>"
val observed = simple_web_rendering_parity_observe(html, 16, 16)
val cpu_stages = simple_web_rendering_parity_stage_records_from_observation(
    "same-composition", "cpu", html, observed
).unwrap()
val cpu = engine2d_rendering_parity_execute_composition(
    "same-composition", observed.composition, cpu_stages, 16, 16,
    "cpu", "execution-cpu", "revision-one", "artifact-cpu",
    observed.degraded, "not-applicable", 1, 1
).unwrap()
expect(cpu.evidence.execution_id).to_equal("execution-cpu")
expect(cpu.evidence.requested_backend).to_equal("cpu")
expect(cpu.output.stages[3].output_checksum).to_equal(cpu_stages[3].output_checksum)

val simd_stages = simple_web_rendering_parity_stage_records_from_observation(
    "same-composition", "cpu_simd", html, observed
).unwrap()
val simd = engine2d_rendering_parity_execute_composition(
    "same-composition", observed.composition, simd_stages, 16, 16,
    "cpu_simd", "execution-cpu-simd", "revision-one",
    "artifact-cpu-simd", observed.degraded, "simd-hit-1", 1, 1
).unwrap()
expect(simd.evidence.execution_id).to_equal("execution-cpu-simd")
expect(simd.evidence.execution_id == cpu.evidence.execution_id).to_be(false)
expect(simd.evidence.simd_execution_receipt).to_equal("simd-hit-1")
expect(simd.output.rgba8).to_equal(cpu.output.rgba8)

val unavailable = engine2d_rendering_parity_execute_composition(
    "same-composition", observed.composition, cpu_stages, 16, 16,
    "backend-that-does-not-exist", "execution-unavailable",
    "revision-one", "artifact-unavailable", observed.degraded,
    "", 1, 1
)
match unavailable:
    Ok(_): fail("unknown backend must not fall back")
    Err(reason): expect(reason).to_contain("backend unavailable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D rendering parity adapter.
- Engine2D rendering parity adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `939f0a625c94a86b154d7be740a5bf1e398eeea5460a7bf9b0725835fbd36940`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `939f0a625c94a86b154d7be740a5bf1e398eeea5460a7bf9b0725835fbd36940`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `939f0a625c94a86b154d7be740a5bf1e398eeea5460a7bf9b0725835fbd36940`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps manifest row names to explicit Engine2D backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts ARGB words to tightly packed straight RGBA bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed length and checksum evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
