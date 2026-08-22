# native_shader_backend_readback_matrix_spec

> @cover src/lib/gc_async_mut/gpu/engine2d/engine.spl 20%

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_shader_backend_readback_matrix_spec

@cover src/lib/gc_async_mut/gpu/engine2d/engine.spl 20%

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/native_shader_backend_readback_matrix_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

@cover src/lib/gc_async_mut/gpu/engine2d/engine.spl 20%
@cover src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl 20%
@cover src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl 20%

Runs the same strict probe + readback parity case through a small backend
config matrix:

- Vulkan on Linux expects `spirv`
- Metal on macOS expects `msl`

The host-specific branch is selected only by config. Off-host runs still assert
typed diagnostics rather than skipping the spec entirely.

## Scenarios

### Native shader backend readback matrix

#### shares the same probe and readback case across Vulkan/Linux and Metal/macOS configs

- Verify: shares the same probe and readback case across Vulkan/Linux and Metal/macOS configs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-RENDERING_NATIVE_SHADER_BACK-001
step("Verify: shares the same probe and readback case across Vulkan/Linux and Metal/macOS configs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
for config in _configs():
    _assert_shared_backend_case(config)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2285b3219b77e63899884aedcb0bf304ab8fee3e64fb3e475b830f7bfefdd80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2285b3219b77e63899884aedcb0bf304ab8fee3e64fb3e475b830f7bfefdd80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2285b3219b77e63899884aedcb0bf304ab8fee3e64fb3e475b830f7bfefdd80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/rendering/native_shader_backend_readback_matrix_spec.spl
mirror: doc/06_spec/02_integration/rendering/native_shader_backend_readback_matrix_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/native_shader_backend_readback_matrix_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/rendering/native_shader_backend_readback_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/native_shader_backend_readback_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
