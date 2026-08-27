# processing_vulkan_fault_native_contract_spec

> Purpose: hold the native Vulkan ProcessingIR fault lane to executed behavior —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_vulkan_fault_native_contract_spec

Purpose: hold the native Vulkan ProcessingIR fault lane to executed behavior —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: hold the native Vulkan ProcessingIR fault lane to executed behavior —
the fault probe's injected-fail lanes must report the exact fail-closed contract
line, and the native gate must refuse to pass when its probe binary is absent.
Audience: simpleos_gpu_host maintainers and the GPU fault-injection owners.

## Scenarios

### native Vulkan ProcessingIR fault evidence contract

#### fails closed with the exact contract line on the injected unavailable lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- inject the unavailable fault and require the exact fail-closed report
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inject the unavailable fault and require the exact fail-closed report")
val (stdout, code) = run_probe("unavailable")
expect(code).to_equal(0)  # oracle: the probe itself reports, it does not crash
expect(stdout).to_contain(
    "VULKAN_FAULT_NATIVE status=pass phase=unavailable fault_active=true " +
    "completed=false reason=vulkan-unavailable values=0 values_exact=false " +
    "hash_sanity=true handle=0 identity=0")  # oracle: full fail-closed contract line, nothing fabricated
```

</details>

#### every injected phase reports its own failure reason with no fabricated output

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- inject submit/readback/mismatch/dispatch phases; each reports its own reason, never completes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inject submit/readback/mismatch/dispatch phases; each reports its own reason, never completes")
var reason = ""
for phase in ["submit", "readback", "mismatch", "dispatch-ineligible"]:
    if phase == "submit": reason = "vulkan-submit-failed"
    elif phase == "readback": reason = "vulkan-readback-failed"
    elif phase == "mismatch": reason = "checksum-mismatch"
    else: reason = "vulkan-dispatch-ineligible"
    val (stdout, _code) = run_probe(phase)
    expect(stdout).to_start_with("VULKAN_FAULT_NATIVE ")  # oracle: probe always reports through the contract channel
    expect(stdout).to_contain("phase=" + phase + " fault_active=true")  # oracle: the injected phase is armed
    expect(stdout).to_contain("completed=false")  # oracle: no fabricated completion
    expect(stdout).to_contain("reason=" + reason)  # oracle: each phase fails with its own documented reason
    expect(stdout).to_contain("values=0 values_exact=false")  # oracle: no fabricated output
```

</details>

#### the native gate fails closed when its probe binary is absent

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- run the gate without a built probe binary; it must block, not pass
   - Expected: file_exists(WRAPPER) is true
   - Expected: code != 0 is true
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the gate without a built probe binary; it must block, not pass")
expect(file_exists(WRAPPER)).to_equal(true)
val (stdout, _stderr, code) = process_run("/bin/sh", [WRAPPER])
if stdout.contains("probe-binary-missing"):
    expect(code != 0).to_equal(true)  # oracle: blocked evidence is a failure, never a pass
    expect(stdout).to_contain("processing_vulkan_fault_native_status=blocked")
    expect(stdout).to_contain("processing_vulkan_fault_native_reason=probe-binary-missing")
else:
    # The native probe binary exists on this host: the gate must fully pass.
    expect(code).to_equal(0)  # oracle: with the real binary the whole fault matrix is green
    expect(stdout).to_contain("processing_vulkan_fault_native_status=pass")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8dc33360bc3b5c86f2df417674f6129c77a9e14742cef8578757faa40d3e8ad2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8dc33360bc3b5c86f2df417674f6129c77a9e14742cef8578757faa40d3e8ad2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8dc33360bc3b5c86f2df417674f6129c77a9e14742cef8578757faa40d3e8ad2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
