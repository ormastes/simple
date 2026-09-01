# Vulkan Engine2D 8K Qualification Contract

> Protects the physical-adapter, exact-readback, retained-batch, and 80-fps

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Engine2D 8K Qualification Contract

Protects the physical-adapter, exact-readback, retained-batch, and 80-fps

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | REQ-GPU-DYN-007, REQ-GPU-DYN-008, REQ-GPU-DYN-012, |
| Source | `test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Protects the physical-adapter, exact-readback, retained-batch, and 80-fps
qualification gates used by the clear, font, and mixed Vulkan profiles.

NFR-GPU-DYN-001, NFR-GPU-DYN-010

## Scenarios

### Vulkan Engine2D 8K qualification contract

#### uses packed font dispatch by default

- Read the font qualification gate
- Require one packed parameter upload and dispatch lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the font qualification gate")
val source = file_read("scripts/check/check-engine2d-vulkan-font-8k.shs")

step("Require one packed parameter upload and dispatch lane")
# @req: REQ-GPU-DYN-008
expect(source).to_contain("ENGINE2D_VULKAN_FONT_MODE:-packed")
expect(source).to_contain("engine2d_vulkan_font_mismatch_count=0")
```

</details>

#### can require physical hardware and the selected latency budget

- Inspect every Vulkan Engine2D profile gate
- Require explicit physical-adapter qualification
- Require an enforceable 80-fps p95 gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect every Vulkan Engine2D profile gate")
val clear = file_read("scripts/check/check-engine2d-vulkan-clear-8k.shs")
val font = file_read("scripts/check/check-engine2d-vulkan-font-8k.shs")
val mixed = file_read("scripts/check/check-engine2d-vulkan-mixed-8k.shs")

step("Require explicit physical-adapter qualification")
# @req: REQ-GPU-DYN-007
expect(clear).to_contain("ENGINE2D_VULKAN_REQUIRE_PHYSICAL")
expect(font).to_contain("ENGINE2D_VULKAN_REQUIRE_PHYSICAL")
expect(mixed).to_contain("ENGINE2D_VULKAN_REQUIRE_PHYSICAL")
expect(clear).to_contain("(discrete|integrated)")
expect(font).to_contain("(discrete|integrated)")
expect(mixed).to_contain("(discrete|integrated)")

step("Require an enforceable 80-fps p95 gate")
# @req: REQ-GPU-DYN-012
expect(clear).to_contain("ENGINE2D_VULKAN_REQUIRE_80FPS")
expect(font).to_contain("ENGINE2D_VULKAN_REQUIRE_80FPS")
expect(mixed).to_contain("ENGINE2D_VULKAN_REQUIRE_80FPS")
expect(clear).to_contain("engine2d_vulkan_within_80fps_budget=true")
expect(font).to_contain("engine2d_vulkan_font_within_80fps_budget=true")
expect(mixed).to_contain("engine2d_vulkan_mixed_within_80fps_budget=true")
```

</details>

#### publishes font adapter provenance with exact evidence

- Read the native font benchmark
- Require device identity and zero-tolerance comparison fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the native font benchmark")
val source = file_read("test/09_baselines/engine2d_vulkan/engine2d_vulkan_font_8k_bench.c")

step("Require device identity and zero-tolerance comparison fields")
# @req: NFR-GPU-DYN-001
expect(source).to_contain("engine2d_vulkan_font_adapter_name=")
expect(source).to_contain("engine2d_vulkan_font_adapter_type=")
expect(source).to_contain("engine2d_vulkan_font_mismatch_count=")
expect(source).to_contain("engine2d_vulkan_font_timed_readback_bytes=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-GPU-DYN-007, REQ-GPU-DYN-008, REQ-GPU-DYN-012,`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GPU-DYN-007`
- `REQ-GPU-DYN-008`
- `REQ-GPU-DYN-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff1eb1c1d51477a2936f6ff8d56459e87a914b99051bc2af4db655f2c0d694d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff1eb1c1d51477a2936f6ff8d56459e87a914b99051bc2af4db655f2c0d694d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff1eb1c1d51477a2936f6ff8d56459e87a914b99051bc2af4db655f2c0d694d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl
mirror: doc/06_spec/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.md (current)
findings: 9 blockers: 0
  narrative=80 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses packed font dispatch by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can require physical hardware and the selected latency budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can require physical hardware and the selected latency budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/vulkan_engine2d_8k_qualification_contract_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes font adapter provenance with exact evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
