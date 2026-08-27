# Processing Cuda Fill Native Contract Specification

> Tests covering direct CUDA ProcessingIR native evidence contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Cuda Fill Native Contract Specification

## Scenarios

### direct CUDA ProcessingIR native evidence contract

#### requires the exact shared 64-element fill fixture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires the exact shared 64-element fill fixture
   - Expected: file_exists(PROBE) is true
   - Expected: indexed_access_present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the exact shared 64-element fill fixture")
val source = file_read(PROBE)
expect(file_exists(PROBE)).to_equal(true)
expect(source).to_contain("processing_ir_execute_cuda_with_executor(")
expect(source).to_contain("val count: i64 = if large or warm: 1048576 else: 64")
expect(source).to_contain("expected_checksum: u64 = if large or warm: 17730434498560 else: 1082179840")
expect(source).to_contain("checksum == expected_checksum and mismatches == 0")
expect(source).to_contain("for actual in result.values:")
expect(source).to_contain("checksum = checksum + actual.to_u64()")
# indexed element access is forbidden: the checksum must fold the whole result
val indexed_access_present = source.contains("result.values[index]")
expect(indexed_access_present).to_equal(false)
```

</details>

#### keeps the policy-threshold workload on the same direct executor

- keeps the policy-threshold workload on the same direct executor


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the policy-threshold workload on the same direct executor")
val source = file_read(PROBE)
val wrapper = file_read(WRAPPER)
expect(source).to_contain("((large or warm or recover) and args.len() != 2)")
expect(source).to_contain("if started_nanos <= 0: return 0")
expect(source).to_contain("val elapsed_us = _elapsed_us(started)")
expect(source).to_contain("elapsed_us > 0")
expect(wrapper).to_contain("large) PROBE_ARG=--large; COUNT=1048576; CHECKSUM=17730434498560")
expect(wrapper).to_contain("warm) PROBE_ARG=--warm; COUNT=1048576; CHECKSUM=17730434498560")
expect(wrapper).to_contain("mode=$MODE completed=true count=$COUNT")
expect(wrapper).to_contain("elapsed_us=[1-9][0-9]*")
expect(wrapper).to_contain("warm_improved=true")
```

</details>

#### requires same-session recovery after deterministic CUDA failures

- requires same-session recovery after deterministic CUDA failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires same-session recovery after deterministic CUDA failures")
val source = file_read(PROBE)
val wrapper = file_read(WRAPPER)
expect(source).to_contain("val recover_readback = args.contains(\"--recover=readback\")")
expect(source).to_contain("val recover_submit = args.contains(\"--recover=submit\")")
expect(source).to_contain("val recover_mismatch = args.contains(\"--recover=mismatch\")")
expect(source).to_contain("\"submit\", \"cuda:submit\", \"cuda-submit-failed\"")
expect(source).to_contain("\"mismatch\", \"cuda:mismatch\", \"checksum-mismatch\"")
expect(source).to_contain("\"readback\", \"cuda:readback\", \"cuda-readback-failed\"")
expect(source).to_contain("failed.reason == expected_reason and failed.values.len() == 0")
expect(source).to_contain("recovered.device_identity == before.device_identity")
expect(source).to_contain("recovered.backend_handle == before.backend_handle")
expect(source).to_contain("executor.shutdown()")
expect(wrapper).to_contain("recovery) RECOVERY_PHASE=readback; RECOVERY_REASON=cuda-readback-failed")
expect(wrapper).to_contain("RECOVERY_PHASE=\nRECOVERY_REASON=")
expect(wrapper).to_contain("recovery-submit) RECOVERY_PHASE=submit; RECOVERY_REASON=cuda-submit-failed")
expect(wrapper).to_contain("recovery-mismatch) RECOVERY_PHASE=mismatch; RECOVERY_REASON=checksum-mismatch")
expect(wrapper).to_contain("PROCESSING_CUDA_RECOVERY status=pass phase=$RECOVERY_PHASE")
expect(wrapper).to_contain(
    "receipt_count=$(printf '%s\\n' \"$output\" | grep -Ec '^PROCESSING_CUDA_RECOVERY ' || true)")
expect(wrapper).to_contain(
    "if [ \"$receipt_count\" -ne 1 ] || [ \"$valid\" -ne 1 ]; then")
expect(wrapper).to_contain("failed_reason=$RECOVERY_REASON failed_count=0 failed_handle=0 failed_identity=0")
expect(wrapper).to_contain("recovered_count=64 recovered_checksum=1082179840 recovered_exact=true")
expect(wrapper).to_contain("identity_stable=true cpu_fallback=false")
```

</details>

#### reuses one CUDA session for the measured warm request

- reuses one CUDA session for the measured warm request


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reuses one CUDA session for the measured warm request")
val source = file_read(PROBE)
val executor = file_read(EXECUTOR)
val platform = file_read(PLATFORM)
val platform_contract = file_read(PLATFORM_CONTRACT)
val daemon = file_read(DAEMON)
val entry = file_read(ENTRY)
expect(source).to_contain("var executor = ProcessingCudaExecutor.create()")
expect(source).to_contain("val cold = processing_ir_execute_cuda_with_executor(")
expect(source).to_contain(
    "cold_reason=" + "{" + "cold.reason} cold_count=" + "{" + "cold.values.len()}")
expect(source).to_contain("val result = processing_ir_execute_cuda_with_executor(")
expect(source).to_contain("executor.shutdown()")
expect(executor).to_contain("if self.session.module_cache > 0:")
expect(executor).to_contain("self.buffer_capacity >= byte_count")
expect(executor).to_contain("self.device_buffer = replacement_device")
expect(executor).to_contain("self.host_buffer = replacement_host")
expect(executor).to_contain("executor.session.launch_kernel_args(")
expect(executor).to_contain("self.session.shutdown()")
expect(executor).to_contain("reason: \"cuda-readback-size-mismatch\"")
expect(executor).to_contain("return \"cuda-executor-closed\"")
expect(executor).to_contain("self.session.activate()")
expect(executor).to_contain("if not dispatch_ok:\n        executor._release_buffers()\n        executor.session.shutdown()")
expect(executor).to_contain("if not copied:\n        executor._release_buffers()\n        executor.session.shutdown()")
expect(source).to_contain("val warm_improved = not warm or elapsed_us < cold_us")
expect(source).to_contain("cold_checksum == expected_checksum and cold_mismatches == 0")
expect(source).to_contain("result.device_identity == cold_identity")
expect(platform).to_contain("cuda_executor: ProcessingCudaExecutor")
expect(platform).to_contain("_execute_processing(self.cuda_executor, ir, backend)")
expect(platform_contract).to_contain("fn shutdown()")
expect(daemon).to_contain("platform.shutdown()")
expect(entry).to_contain("SimpleOsGpuHostAllPlatform.create()")
```

</details>

#### requires device provenance and rejects fallback

- requires device provenance and rejects fallback
   - Expected: executor does not contain `values.push(raw_read_i32`
   - Expected: executor does not contain `processing_ir_execute_cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires device provenance and rejects fallback")
val source = file_read(PROBE)
val wrapper = file_read(WRAPPER)
val executor = file_read(EXECUTOR)
expect(source).to_contain("result.backend_handle > 0 and result.device_identity > 0")
expect(executor).to_contain("cuda_memcpy_dtoh(")
expect(executor).to_contain("raw_read_u32s(host_ptr, ir.element_count)")
expect(executor.contains("values.push(raw_read_i32")).to_equal(false)
expect(executor.contains("processing_ir_execute_cpu")).to_equal(false)
expect(wrapper).to_contain("backend=cuda readback_source=device_readback")
expect(wrapper).to_contain("handle=[1-9][0-9]* identity=[1-9][0-9]*")
expect(wrapper).to_contain(
    "before_count=64 before_checksum=1082179840 before_exact=true")
expect(wrapper).to_contain(
    "recovered_count=64 recovered_checksum=1082179840 recovered_exact=true")
expect(wrapper).to_contain("cpu_fallback=false")
expect(wrapper).to_contain("timeout -k 5 \"$TIMEOUT_SECONDS\"")
expect(wrapper).to_contain("probe_rc=$?")
expect(wrapper).to_contain("exit \"$probe_rc\"")
expect(wrapper).to_contain("processing_cuda_fill_native_reason=probe-failed")
expect(wrapper).to_contain("processing_cuda_fill_native_reason=invalid-receipt")
```

</details>

#### uses length-tracked native PTX and kernel-name ABIs

- uses length-tracked native PTX and kernel-name ABIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses length-tracked native PTX and kernel-name ABIs")
val source = file_read(CUDA)
expect(source).to_contain("if rt_is_interpreter_runtime()")
expect(source).to_contain("fn cuda_ctx_set_current(ctx: i64) -> i64:")
expect(source).to_contain("rt_cuda_module_load_data_array(bytes)")
expect(source).to_contain("rt_cuda_launch_kernel_name_array(")
expect(source).to_contain("module, name_bytes,")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering direct CUDA ProcessingIR native evidence contract.
- direct CUDA ProcessingIR native evidence contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `7c031de3e55518780b2f4d61a2bc251e5ae932eec196658aa74a0d26414ef419`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c031de3e55518780b2f4d61a2bc251e5ae932eec196658aa74a0d26414ef419`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c031de3e55518780b2f4d61a2bc251e5ae932eec196658aa74a0d26414ef419`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the exact shared 64-element fill fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the policy-threshold workload on the same direct executor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cuda_fill_native_contract_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires same-session recovery after deterministic CUDA failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
