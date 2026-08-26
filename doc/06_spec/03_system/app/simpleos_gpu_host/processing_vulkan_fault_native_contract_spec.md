# Processing Vulkan Fault Native Contract Specification

> Tests covering native Vulkan ProcessingIR fault evidence contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Vulkan Fault Native Contract Specification

## Scenarios

### native Vulkan ProcessingIR fault evidence contract

#### requires exact device output and positive native provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires exact device output and positive native provenance
   - Expected: file_exists(PROBE) is true
   - Expected: source does not contain `result.values[index]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires exact device output and positive native provenance")
val source = file_read(PROBE)
expect(file_exists(PROBE)).to_equal(true)
expect(source).to_contain("result.completed and result.reason == \"ok\" and values_exact")
expect(source).to_contain("result.backend_handle > 0 and result.device_identity > 0")
expect(source).to_contain("processing_ir_fill_u32(64, value)")
expect(source).to_contain("processing_vulkan_device_identity(\"abc\") == 96354")
expect(source).to_contain("hash_sanity and not fault_active")
expect(source).to_contain("fn _values_exact(values: [u32], expected_count: i64, expected_value: u32) -> bool:")
expect(source).to_contain("_values_exact(result.values, 64, value)")
expect(source.contains("result.values[index]")).to_equal(false)
```

</details>

#### fails closed for every injected phase

- fails closed for every injected phase


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed for every injected phase")
val source = file_read(PROBE)
for phase in ["unavailable", "init", "submit", "readback", "mismatch", "dispatch-ineligible"]:
    expect(source).to_contain("phase == \"" + phase + "\"")
for phase in ["none", "unavailable", "init", "submit", "readback", "mismatch", "dispatch-ineligible"]:
    expect(source).to_contain("if arg == \"--phase=" + phase + "\": return \"" + phase + "\"")
expect(source).to_contain("if arg == \"--recover=submit\": return \"recover-submit\"")
expect(source).to_contain("not result.completed and result.reason == _expected_reason(phase)")
expect(source).to_contain("result.values.len() == 0 and result.backend_handle == 0")
expect(source).to_contain("result.device_identity == 0 and fault_active")
```

</details>

#### runs one default and six bounded isolated native processes

- runs one default and six bounded isolated native processes
   - Expected: probe_source does not contain `.starts_with(`
   - Expected: file_exists(WRAPPER) is true
   - Expected: source.split("2>&1").len() - 1 equals `3`
   - Expected: source.split("set +e").len() - 1 equals `3`
   - Expected: source.split("code=$?").len() - 1 equals `3`
   - Expected: source.split("set -e\n").len() - 1 equals `3`
   - Expected: source.split("[ \"$code\" -eq 0 ] || return \"$code\"").len() - 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs one default and six bounded isolated native processes")
val probe_source = file_read(PROBE)
val source = file_read(WRAPPER)
expect(probe_source).to_contain("fn _phase_from_args(args: [text]) -> text:")
expect(probe_source.contains(".starts_with(")).to_equal(false)
expect(file_exists(WRAPPER)).to_equal(true)
expect(source).to_contain("timeout -k 5 \"$TIMEOUT_SECONDS\"")
expect(source.split("2>&1").len() - 1).to_equal(3)
expect(source.split("set +e").len() - 1).to_equal(3)
expect(source.split("code=$?").len() - 1).to_equal(3)
expect(source.split("set -e\n").len() - 1).to_equal(3)
expect(source.split("[ \"$code\" -eq 0 ] || return \"$code\"").len() - 1).to_equal(2)
expect(source).to_contain("[ \"$recovery_code\" -eq 0 ]")
expect(source).to_contain("env -u SIMPLE_GPU_FAULT_INJECT_SKIP_MATCHES SIMPLE_GPU_TEST=1 SIMPLE_GPU_FAULT_INJECT=\"vulkan:$phase\"")
expect(source).to_contain("run_case none")
expect(source).to_contain("for phase in unavailable init submit readback mismatch dispatch-ineligible")
expect(source).to_contain("processing_vulkan_fault_native_status=pass")
expect(source).to_contain("grep -Ec '^VULKAN_FAULT_NATIVE '")
expect(source).to_contain("[ \"$total\" -eq 1 ] && [ \"$valid\" -eq 1 ]")
expect(source).to_contain("hash_sanity=true handle=[1-9][0-9]* identity=[1-9][0-9]*$")
expect(source).to_contain("\"$PROBE_BIN\" --recover=submit")
expect(source).to_contain("VULKAN_FAULT_RECOVERY status=pass")
expect(source).to_contain("grep -Ec '^VULKAN_FAULT_RECOVERY '")
expect(source).to_contain("[ \"$recovery_total\" -eq 1 ] && [ \"$recovery_valid\" -eq 1 ]")
expect(probe_source).to_contain("recovered.device_identity == before.device_identity")
expect(source).to_contain("identity_stable=true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native Vulkan ProcessingIR fault evidence contract.
- native Vulkan ProcessingIR fault evidence contract

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

- Canonical SPipe generation for source `9378738d76bdbd5d434b591e4e75e4482a4ac6efdd6b7e9473443c2a728a467b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9378738d76bdbd5d434b591e4e75e4482a4ac6efdd6b7e9473443c2a728a467b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9378738d76bdbd5d434b591e4e75e4482a4ac6efdd6b7e9473443c2a728a467b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires exact device output and positive native provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for every injected phase' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs one default and six bounded isolated native processes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
