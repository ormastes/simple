# X25519mlkem768 Vulkan Shader Contract Specification

> Tests covering X25519MLKEM768 Vulkan NTT shader contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Vulkan Shader Contract Specification

## Scenarios

### X25519MLKEM768 Vulkan NTT shader contract

#### should use ping-pong workgroup storage and an explicit zeta buffer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should use ping-pong workgroup storage and an explicit zeta buffer
- Inspect the forward shader storage and zeta-table contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should use ping-pong workgroup storage and an explicit zeta buffer")
step("Inspect the forward shader storage and zeta-table contract")
val shader = rt_file_read_text(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp") ?? ""
expect(shader).to_contain("layout(set = 0, binding = 2, std430) readonly buffer ZetaTable")
expect(shader).to_contain("shared int stage_a[256]")
expect(shader).to_contain("shared int stage_b[256]")
expect(shader).to_contain("if (tid < 128u)")
expect(shader).to_contain("stage_b[lower_tid] = next_lower")
expect(shader).to_contain("stage_b[upper_tid] = next_upper")
expect(shader).to_contain("stage_a[lower_tid] = next_lower")
expect(shader).to_contain("stage_a[upper_tid] = next_upper")
expect(shader).to_contain("memoryBarrierShared()")
expect(shader).to_contain("barrier()")
expect(shader.contains("stage_b[tid] = next_value")).to_be(false)
expect(shader.contains("const int zetas[128]")).to_be(false)
expect(shader).to_contain("int magnitude = -(value + 1)")
expect(shader).to_contain("((magnitude % 3329) + 1) % 3329")
expect(shader.contains("int reduced = value % 3329")).to_be(false)
```

</details>

#### should keep all stage barriers uniform and expose bounded diagnostics

- should keep all stage barriers uniform and expose bounded diagnostics
- Inspect stage bounds and uniform shared-memory barrier ordering


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should keep all stage barriers uniform and expose bounded diagnostics")
step("Inspect stage bounds and uniform shared-memory barrier ordering")
val shader = rt_file_read_text(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.comp") ?? ""
expect(shader).to_contain("uint stage_count")
expect(shader).to_contain("min(parameters.stage_count, 7u)")
expect(shader).to_contain("stage < stages")
expect(shader).to_contain("uint len = 128u >> stage")
expect(shader).to_contain("uint zeta_base = 1u << stage")
val barrier = shader.index_of("memoryBarrierShared()")
val conditional_write = shader.index_of("if (current_is_a)")
expect(barrier).to_be_greater_than(conditional_write)
```

</details>

#### should bind the probe to the same three-buffer and seven-stage ABI

- should bind the probe to the same three-buffer and seven-stage ABI
- Compare the native probe bindings with the shader stage ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should bind the probe to the same three-buffer and seven-stage ABI")
step("Compare the native probe bindings with the shader stage ABI")
val probe = rt_file_read_text(
    "test/fixtures/crypto/x25519mlkem768/vulkan_ntt_probe.c") ?? ""
expect(probe).to_contain("VkDescriptorSetLayoutBinding bindings[3]")
expect(probe).to_contain("VkDescriptorBufferInfo buffer_infos[3]")
expect(probe).to_contain("Parameters parameters = {BATCH, stage_count}")
expect(probe).to_contain("scalar_ntt(&expected[p * N], stage_count)")
expect(probe).to_contain("[stage-count:1..7]")
expect(probe).to_contain("requested_stages > 7")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 Vulkan NTT shader contract.
- X25519MLKEM768 Vulkan NTT shader contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `333848849f1ccabcdadf4e56510f4b2b94cf561efb4186cbbfae94abebd93ab4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `333848849f1ccabcdadf4e56510f4b2b94cf561efb4186cbbfae94abebd93ab4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `333848849f1ccabcdadf4e56510f4b2b94cf561efb4186cbbfae94abebd93ab4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use ping-pong workgroup storage and an explicit zeta buffer' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use ping-pong workgroup storage and an explicit zeta buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep all stage barriers uniform and expose bounded diagnostics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep all stage barriers uniform and expose bounded diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind the probe to the same three-buffer and seven-stage ABI' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_vulkan_shader_contract_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind the probe to the same three-buffer and seven-stage ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
