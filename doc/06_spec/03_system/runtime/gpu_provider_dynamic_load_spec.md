# Gpu Provider Dynamic Load Specification

> Tests covering dynamic GPU providers without rebuilding the Simple host.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Provider Dynamic Load Specification

## Scenarios

### dynamic GPU providers without rebuilding the Simple host

#### should expose one fail-closed provider admission contract

- should expose one fail-closed provider admission contract
- Inspect the dynamic provider admission checker
- Verify ABI capability and operation validation happen before use
- Verify replacement is exercised without rebuilding the harness


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose one fail-closed provider admission contract")
step("Inspect the dynamic provider admission checker")
val source = file_read(GPU_PROVIDER_CHECK)

step("Verify ABI capability and operation validation happen before use")
expect(source).to_contain("simple_gpu_provider_query_v1")
expect(source).to_contain("gpu_provider_query_only_export=true")
expect(source).to_contain("gpu_provider_c_cpp_header_compatible=true")
expect(source).to_contain("gpu_provider_incomplete_surface_rejected=true")
expect(source).to_contain("gpu_provider_incomplete_ownership_rejected=true")
expect(source).to_contain("gpu_provider_readback_descriptor_corruption_rejected=true")
expect(source).to_contain("gpu_provider_receipt_corruption_rejected=true")
expect(source).to_contain("cuda_provider_missing_operation_fails_closed=true")

step("Verify replacement is exercised without rebuilding the harness")
expect(source).to_contain("rt_gpu_provider_unload")
expect(source).to_contain("gpu_provider_replacement_without_host_rebuild=true")
```

</details>

#### should load reject dispatch unload and replace Vulkan and CUDA providers

- should load reject dispatch unload and replace Vulkan and CUDA providers
- Build two compatible providers and invalid adjacent fixtures
- Require successful operation dispatch and fail-closed rejection
   - Expected: code equals `0`
   - Expected: stderr equals ``
- Require unload and replacement through the unchanged host


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should load reject dispatch unload and replace Vulkan and CUDA providers")
if not is_linux():
    pending("The focused fixture currently compiles ELF shared providers with cc")
else:
    step("Build two compatible providers and invalid adjacent fixtures")
    val (stdout, stderr, code) = run_checker(GPU_PROVIDER_CHECK)

    step("Require successful operation dispatch and fail-closed rejection")
    expect(code).to_equal(0)
    expect(stderr).to_equal("")
    expect(stdout).to_contain("gpu_provider_dynamic_load=true")
    expect(stdout).to_contain("gpu_provider_query_only_export=true")
    expect(stdout).to_contain("gpu_provider_c_cpp_header_compatible=true")
    expect(stdout).to_contain("gpu_provider_owned_session_lifecycle=true")
    expect(stdout).to_contain("gpu_provider_owned_resource_lifecycle=true")
    expect(stdout).to_contain("gpu_provider_owned_completion_lifecycle=true")
    expect(stdout).to_contain("gpu_provider_cross_session_rejected=true")
    expect(stdout).to_contain("gpu_provider_duplicate_handle_rejected=true")
    expect(stdout).to_contain("gpu_provider_concurrent_release_busy=true")
    expect(stdout).to_contain("gpu_provider_session_close_with_children_busy=true")
    expect(stdout).to_contain("gpu_provider_busy_unload_rejected=true")
    expect(stdout).to_contain("cuda_provider_operation_dispatch=true")
    expect(stdout).to_contain("gpu_provider_wrong_abi_rejected=true")
    expect(stdout).to_contain("gpu_provider_wrong_backend_rejected=true")
    expect(stdout).to_contain("gpu_provider_incomplete_surface_rejected=true")
    expect(stdout).to_contain("gpu_provider_incomplete_ownership_rejected=true")
    expect(stdout).to_contain("gpu_provider_readback_descriptor_corruption_rejected=true")
    expect(stdout).to_contain("gpu_provider_receipt_corruption_rejected=true")
    expect(stdout).to_contain("gpu_provider_path_with_spaces=true")
    expect(stdout).to_contain("gpu_provider_path_snapshot_survives_unload=true")

    step("Require unload and replacement through the unchanged host")
    expect(stdout).to_contain("gpu_provider_unload_reload=true")
    expect(stdout).to_contain("gpu_provider_replacement_without_host_rebuild=true")
    expect(stdout).to_contain("gpu_provider_concurrent_registry_access=true")
    expect(stdout).to_contain("gpu_provider_static_dependency=false")
```

</details>

#### should preserve zero bytes across the Metal provider boundary

- should preserve zero bytes across the Metal provider boundary
- Build the complete wrong-ABI and incomplete Metal providers
- Require core-owned RuntimeValue and length-delimited byte adaptation
   - Expected: code equals `0`
   - Expected: stderr equals ``
- Require invalid Metal providers to remain unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve zero bytes across the Metal provider boundary")
if not is_linux():
    pending("The host-independent Metal provider fixture currently uses ELF shared libraries")
else:
    step("Build the complete wrong-ABI and incomplete Metal providers")
    val (stdout, stderr, code) = run_checker(METAL_PROVIDER_CHECK)

    step("Require core-owned RuntimeValue and length-delimited byte adaptation")
    expect(code).to_equal(0)
    expect(stderr).to_equal("")
    expect(stdout).to_contain("metal_provider_runtime_values_decoded_by_core=true")
    expect(stdout).to_contain("metal_provider_raw_bytes_length_delimited=true")

    step("Require invalid Metal providers to remain unavailable")
    expect(stdout).to_contain("metal_provider_wrong_abi_rejected=true")
    expect(stdout).to_contain("metal_provider_incomplete_surface_rejected=true")
    expect(stdout).to_contain("metal_provider_static_dependency=false")
```

</details>

#### should survive intensive replacement failure and contention cycles

- should survive intensive replacement failure and contention cycles
- Run bounded lifecycle and contention stress through one host executable
- Require stable admission across sixty-four provider replacements
   - Expected: code equals `0`
   - Expected: stderr equals ``
- Require cached failure and explicit-unload recovery semantics
- Require sixteen thousand concurrent reads without corruption


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should survive intensive replacement failure and contention cycles")
if not is_linux():
    pending("The intensive fixture currently compiles ELF shared providers with cc")
else:
    step("Run bounded lifecycle and contention stress through one host executable")
    val (stdout, stderr, code) = run_intensive_checker()

    step("Require stable admission across sixty-four provider replacements")
    expect(code).to_equal(0)
    expect(stderr).to_equal("")
    expect(stdout).to_contain("replacement_cycles=64")
    expect(stdout).to_contain("env_change_requires_unload=true")

    step("Require cached failure and explicit-unload recovery semantics")
    expect(stdout).to_contain("failed_admission_cached=true")
    expect(stdout).to_contain("failed_admission_recovers_after_unload=true")
    expect(stdout).to_contain("unknown_backend_rejected=true")
    expect(stdout).to_contain("empty_path_unloaded=true")
    expect(stdout).to_contain("oversized_path_rejected=true")

    step("Require sixteen thousand concurrent reads without corruption")
    expect(stdout).to_contain("concurrent_threads=16")
    expect(stdout).to_contain("concurrent_calls=16000")
    expect(stdout).to_contain("concurrent_failures=0")
    expect(stdout).to_contain("gpu_provider_intensive_status=pass")
```

</details>

#### should reject malformed Metal values across repeated adapter calls

- should reject malformed Metal values across repeated adapter calls
- Run malformed-value and repeated-call checks through the core adapters
- Require empty source invalid bytes and length mismatches to fail closed
   - Expected: code equals `0`
   - Expected: stderr equals ``
- Require failed downloads to preserve caller-owned output
- Require one thousand stable adapter cycles


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject malformed Metal values across repeated adapter calls")
if not is_linux():
    pending("The intensive Metal adapter fixture currently compiles an ELF provider with cc")
else:
    step("Run malformed-value and repeated-call checks through the core adapters")
    val (stdout, stderr, code) = run_intensive_metal_checker()

    step("Require empty source invalid bytes and length mismatches to fail closed")
    expect(code).to_equal(0)
    expect(stderr).to_equal("")
    expect(stdout).to_contain("metal_provider_empty_shader_rejected=true")
    expect(stdout).to_contain("metal_provider_invalid_byte_values_rejected=true")
    expect(stdout).to_contain("metal_provider_length_mismatch_rejected=true")

    step("Require failed downloads to preserve caller-owned output")
    expect(stdout).to_contain("metal_provider_failed_download_preserves_output=true")

    step("Require one thousand stable adapter cycles")
    expect(stdout).to_contain("metal_provider_adapter_cycles=1000")
    expect(stdout).to_contain("metal_provider_intensive_status=pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/runtime/gpu_provider_dynamic_load_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dynamic GPU providers without rebuilding the Simple host.
- dynamic GPU providers without rebuilding the Simple host

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e4c3666abf83cf1369b25a9b274643281b2b2e6ef82d8d5903d104bd2f74dc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e4c3666abf83cf1369b25a9b274643281b2b2e6ef82d8d5903d104bd2f74dc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e4c3666abf83cf1369b25a9b274643281b2b2e6ef82d8d5903d104bd2f74dc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/runtime/gpu_provider_dynamic_load_spec.spl
mirror: doc/06_spec/03_system/runtime/gpu_provider_dynamic_load_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/runtime/gpu_provider_dynamic_load_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/runtime/gpu_provider_dynamic_load_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose one fail-closed provider admission contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose one fail-closed provider admission contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load reject dispatch unload and replace Vulkan and CUDA providers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should load reject dispatch unload and replace Vulkan and CUDA providers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve zero bytes across the Metal provider boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve zero bytes across the Metal provider boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should survive intensive replacement failure and contention cycles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/runtime/gpu_provider_dynamic_load_spec.spl:143:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed Metal values across repeated adapter calls' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
