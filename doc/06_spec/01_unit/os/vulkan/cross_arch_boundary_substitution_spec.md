# Cross Arch Boundary Substitution Specification

> Tests covering cross-architecture boundary substitution guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross Arch Boundary Substitution Specification

## Scenarios

### cross-architecture boundary substitution guard

#### accepts a same-arch comparison of a command-stream capture

- build two x86_64 command-stream captures
- assert the comparison is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-VULKAN-CROSS-ARCH-001
# @req REQ-VULKAN-CROSS-ARCH-002
step("build two x86_64 command-stream captures")
val left = arch_boundary_capture(
    "vulkan.submit.command_stream@1",
    "x86_64/intel_gen12/ovmf-pflash",
    "x86_64",
    true
)
val right = arch_boundary_capture(
    "vulkan.submit.command_stream@1",
    "x86_64/intel_gen12/ovmf-pflash",
    "x86_64",
    true
)

step("assert the comparison is valid")
assert_true(cross_arch_comparison_is_valid(left, right))
assert_equal(cross_arch_comparison_rejections(left, right).len(), 0)
```

</details>

#### rejects an aarch64-captured command stream compared against an x86_64-captured one

- build an x86_64 command-stream capture (real for this repo today)
- build an aarch64 command-stream capture under a different environment_profile
- assert the cross-arch substitution is rejected, not silently accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build an x86_64 command-stream capture (real for this repo today)")
val x86_capture = arch_boundary_capture(
    "vulkan.submit.command_stream@1",
    "x86_64/intel_gen12/ovmf-pflash",
    "x86_64",
    true
)

step("build an aarch64 command-stream capture under a different environment_profile")
val aarch64_capture = arch_boundary_capture(
    "vulkan.submit.command_stream@1",
    "aarch64/adreno/edk2-aavmf",
    "aarch64",
    true
)

step("assert the cross-arch substitution is rejected, not silently accepted")
val failures = cross_arch_comparison_rejections(x86_capture, aarch64_capture)
assert_false(cross_arch_comparison_is_valid(x86_capture, aarch64_capture))
assert_true(failures.len() > 0)
assert_true(failures[0].contains("cross-arch substitution rejected"))
```

</details>

#### allows a cross-arch comparison ONLY for the declared arch-invariant SPIR-V boundary

- build an x86_64 and an aarch64 SPIR-V binary capture
- assert SPIR-V is arch-invariant and the cross-arch comparison is accepted
- assert readback images are NOT arch-invariant


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build an x86_64 and an aarch64 SPIR-V binary capture")
val x86_spirv = arch_boundary_capture(
    "vulkan.shader.spirv_binary@1",
    "x86_64/intel_gen12/ovmf-pflash",
    "x86_64",
    true
)
val aarch64_spirv = arch_boundary_capture(
    "vulkan.shader.spirv_binary@1",
    "aarch64/adreno/edk2-aavmf",
    "aarch64",
    true
)

step("assert SPIR-V is arch-invariant and the cross-arch comparison is accepted")
assert_true(boundary_is_arch_invariant("vulkan.shader.spirv_binary@1"))
assert_true(cross_arch_comparison_is_valid(x86_spirv, aarch64_spirv))

step("assert readback images are NOT arch-invariant")
assert_false(boundary_is_arch_invariant("vulkan.present.readback_image@1"))
```

</details>

#### reports true arch coverage of 1 when only x86_64 executed, not a claimed 3

- build a capture list where only x86_64 actually executed
- assert the coverage predicate reports 1 arch, not the claimed 3
- assert coverage becomes 3 only once all three actually captured


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a capture list where only x86_64 actually executed")
val only_x86 = [
    arch_boundary_capture("vulkan.submit.command_stream@1", "x86_64/intel_gen12/ovmf-pflash", "x86_64", true),
    arch_boundary_capture("vulkan.submit.command_stream@1", "aarch64/adreno/edk2-aavmf", "aarch64", false),
    arch_boundary_capture("vulkan.submit.command_stream@1", "riscv64/img_bxe/opensbi", "riscv64", false)
]

step("assert the coverage predicate reports 1 arch, not the claimed 3")
val covered = arch_coverage_count("vulkan.submit.command_stream@1", only_x86)
assert_equal(covered, 1)
assert_false(covered == 3)

step("assert coverage becomes 3 only once all three actually captured")
val all_three = [
    arch_boundary_capture("vulkan.submit.command_stream@1", "x86_64/intel_gen12/ovmf-pflash", "x86_64", true),
    arch_boundary_capture("vulkan.submit.command_stream@1", "aarch64/adreno/edk2-aavmf", "aarch64", true),
    arch_boundary_capture("vulkan.submit.command_stream@1", "riscv64/img_bxe/opensbi", "riscv64", true)
]
assert_equal(arch_coverage_count("vulkan.submit.command_stream@1", all_three), 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cross-architecture boundary substitution guard.
- cross-architecture boundary substitution guard

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

- `REQ-VULKAN-CROSS-ARCH-001`
- `REQ-VULKAN-CROSS-ARCH-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db5beeab5b751880e144a2f7c47d0d7955ffb6fd2f9a6921b8f1650eb50a3f12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db5beeab5b751880e144a2f7c47d0d7955ffb6fd2f9a6921b8f1650eb50a3f12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db5beeab5b751880e144a2f7c47d0d7955ffb6fd2f9a6921b8f1650eb50a3f12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a same-arch comparison of a command-stream capture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an aarch64-captured command stream compared against an x86_64-captured one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows a cross-arch comparison ONLY for the declared arch-invariant SPIR-V boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
