# Vulkan Sffi Completion Recovery Contract Specification

> Tests covering Vulkan SFFI completion recovery contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Sffi Completion Recovery Contract Specification

## Scenarios

### Vulkan SFFI completion recovery contract

#### classifies uncertain submit errors and uses device idle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies uncertain submit errors and uses device idle
   - Expected: command does not contain `queue_wait_idle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies uncertain submit errors and uses device idle")
val command = file_read("src/compiler_rust/runtime/src/value/gpu_vulkan/vulkan_sffi/command.rs").replace("\r\n", "\n")

expect(command).to_contain("submit_definitely_not_accepted")
expect(command).to_contain("if !submit_definitely_not_accepted(e)")
expect(command).to_contain("state.submitted_once = true")
expect(command).to_contain("state.completion_unknown = true")
expect(command).to_contain("state.device.wait_hardware_idle()")
expect(command.contains("queue_wait_idle")).to_equal(false)
```

</details>

#### clears uncertainty only after successful device sync

- clears uncertainty only after successful device sync


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears uncertainty only after successful device sync")
val device = file_read("src/compiler_rust/runtime/src/value/gpu_vulkan/vulkan_sffi/device.rs").replace("\r\n", "\n")

expect(device).to_contain("match device.wait_hardware_idle()")
expect(device).to_contain("COMMAND_BUFFER_REGISTRY")
expect(device).to_contain("Arc::ptr_eq(&state.device, &device)")
expect(device).to_contain("state.completion_unknown = false")
expect(device).to_contain("while command buffers are live")
```

</details>

#### serializes device idle with every distinct queue

- serializes device idle with every distinct queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes device idle with every distinct queue")
val device = file_read("src/compiler_rust/runtime/src/vulkan/device.rs").replace("\r\n", "\n")

expect(device).to_contain("let _compute_queue = self.compute_queue.lock()")
expect(device).to_contain("let _graphics_queue = graphics_queue.map(|queue| queue.lock())")
expect(device).to_contain("let _present_queue = self")
expect(device).to_contain("Arc::ptr_eq(queue, &self.compute_queue)")
expect(device).to_contain(".device_wait_idle()")
```

</details>

#### leaks presentation resources when idle recovery fails

- leaks presentation resources when idle recovery fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaks presentation resources when idle recovery fails")
val swapchain = file_read("src/compiler_rust/runtime/src/vulkan/swapchain.rs").replace("\r\n", "\n")
expect(swapchain).to_contain(
    "if let Err(error) = self.device.wait_idle() " + "{" +
    "\n                tracing::error!(\"Leaking Vulkan swapchain after failed idle recovery: " + "{" + "error" + "}" + "\");" +
    "\n                return;\n            " + "}" +
    "\n\n            // Destroy image views"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan SFFI completion recovery contract.
- Vulkan SFFI completion recovery contract

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

- Canonical SPipe generation for source `b07c80e9dc1ee3f8d601baee30e89ed86bd485153a927e33af7a60eaa9a14956`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b07c80e9dc1ee3f8d601baee30e89ed86bd485153a927e33af7a60eaa9a14956`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b07c80e9dc1ee3f8d601baee30e89ed86bd485153a927e33af7a60eaa9a14956`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.spl
mirror: doc/06_spec/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies uncertain submit errors and uses device idle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears uncertainty only after successful device sync' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/check/vulkan_sffi_completion_recovery_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes device idle with every distinct queue' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
