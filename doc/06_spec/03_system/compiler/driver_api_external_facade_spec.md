# Driver Api External Facade Specification

> Tests covering Driver API External Facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Api External Facade Specification

## Scenarios

### Driver API External Facade

#### compile_to_smf writes an smf artifact for a direct external caller

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compile_to_smf writes an smf artifact for a direct external caller
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compile_to_smf writes an smf artifact for a direct external caller")
val src_path = "/tmp/sml_driver_api_compile_to_smf.spl"
val out_path = "/tmp/sml_driver_api_compile_to_smf.smf"
delete_file(out_path)
write_file(src_path, "fn main(): 7")

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### check_file returns success for a valid source file

- check_file returns success for a valid source file
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_file returns success for a valid source file")
val src_path = "/tmp/sml_driver_api_check_ok.spl"
write_file(src_path, "fn main(): 1 + 2")

val result = check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
```

</details>

#### parse_sdn_file returns success for a readable sdn file

- parse_sdn_file returns success for a readable sdn file
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_sdn_file returns success for a readable sdn file")
val sdn_path = "/tmp/sml_driver_api_parse_ok.sdn"
val content = "root:" + NL + "  name: \"driver-api\""
write_file(sdn_path, content)

val result = parse_sdn_file(sdn_path)

expect(result.is_success()).to_equal(true)
delete_file(sdn_path)
```

</details>

#### aot_c_file writes an empty c backend artifact file for a direct external caller

- aot_c_file writes an empty c backend artifact file for a direct external caller
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_c_file writes an empty c backend artifact file for a direct external caller")
val src_path = "/tmp/sml_driver_api_aot_c.spl"
val out_path = "/tmp/sml_driver_api_aot_c.cpp"
delete_file(out_path)
write_file(src_path, "fn main(): 9")

val result = aot_c_file(src_path, out_path)

expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_vhdl_file writes a VHDL artifact for a direct external caller

- aot_vhdl_file writes a VHDL artifact for a direct external caller
   - Expected: result.is_success() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_vhdl_file writes a VHDL artifact for a direct external caller")
val src_path = "/tmp/sml_driver_api_aot_vhdl.spl"
val out_path = "/tmp/sml_driver_api_aot_vhdl.vhd"
delete_file(out_path)
write_file(src_path, "fn add(a: i32, b: i32) -> i32:\n    a + b")

val result = aot_vhdl_file(src_path, out_path)

expect(result.is_success()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
expect(rt_file_read_text(out_path)).to_contain("entity add is")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### aot_native_project_with_backend fails fast with a clear runtime error

- aot_native_project_with_backend fails fast with a clear runtime error
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aot_native_project_with_backend fails fast with a clear runtime error")
val src_path = "/tmp/sml_driver_api_project_fail.spl"
val out_path = "/tmp/sml_driver_api_project_fail.bin"
write_file(src_path, "fn main(): 11")

val result = aot_native_project_with_backend(["/tmp"], src_path, out_path, "llvm-lib", false, false, 0)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("not supported")

delete_file(src_path)
delete_file(out_path)
```

</details>

#### backend helper symbols import cleanly for a direct external caller

- backend helper symbols import cleanly for a direct external caller
   - Expected: llvm_result.is_success() is true
   - Expected: rt_file_exists(llvm_out_path) is true
   - Expected: cuda_result.is_success() is true
   - Expected: rt_file_exists(cuda_out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("backend helper symbols import cleanly for a direct external caller")
val src_path = "/tmp/sml_driver_api_backend_helpers.spl"
val llvm_out_path = "/tmp/sml_driver_api_backend_helpers.ll"
val cuda_out_path = "/tmp/sml_driver_api_backend_helpers.cu"
write_file(src_path, "fn main(): 13")
delete_file(llvm_out_path)
delete_file(cuda_out_path)

val llvm_result = aot_llvm_file(src_path, llvm_out_path)
val cuda_result = aot_cuda_file(src_path, cuda_out_path)

expect(llvm_result.is_success()).to_equal(true)
expect(rt_file_exists(llvm_out_path)).to_equal(true)
expect(cuda_result.is_success()).to_equal(true)
expect(rt_file_exists(cuda_out_path)).to_equal(true)

delete_file(src_path)
delete_file(llvm_out_path)
delete_file(cuda_out_path)
```

</details>

#### grouped compile helper imports resolve cleanly for a direct external caller

- grouped compile helper imports resolve cleanly for a direct external caller
   - Expected: compile_result.is_success() is true
   - Expected: smf_result.is_ok() is true
   - Expected: rt_file_exists(smf_out_path) is true
   - Expected: check_result.is_success() is true
   - Expected: sdn_result.is_success() is true
   - Expected: c_result.is_success() is true
   - Expected: rt_file_exists(c_out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grouped compile helper imports resolve cleanly for a direct external caller")
val src_path = "/tmp/sml_driver_api_grouped_compile.spl"
val smf_out_path = "/tmp/sml_driver_api_grouped_compile.smf"
val c_out_path = "/tmp/sml_driver_api_grouped_compile.cpp"
val sdn_path = "/tmp/sml_driver_api_grouped_compile.sdn"
write_file(src_path, "fn main(): 17")
write_file(sdn_path, "root:" + NL + "  name: \"grouped-compile\"")
delete_file(smf_out_path)
delete_file(c_out_path)

val compile_result = compile_file(src_path)
val smf_result = compile_to_smf(src_path, smf_out_path)
val check_result = check_file(src_path)
val sdn_result = parse_sdn_file(sdn_path)
val c_result = aot_c_file(src_path, c_out_path)

expect(compile_result.is_success()).to_equal(true)
expect(smf_result.is_ok()).to_equal(true)
expect(rt_file_exists(smf_out_path)).to_equal(true)
expect(check_result.is_success()).to_equal(true)
expect(sdn_result.is_success()).to_equal(true)
expect(sdn_result.get_value()).to_contain("grouped-compile")
expect(c_result.is_success()).to_equal(true)
expect(rt_file_exists(c_out_path)).to_equal(true)

delete_file(src_path)
delete_file(smf_out_path)
delete_file(c_out_path)
delete_file(sdn_path)
```

</details>

#### grouped backend helper imports resolve cleanly for a direct external caller

- grouped backend helper imports resolve cleanly for a direct external caller
   - Expected: llvm_native_result.is_success() is false
   - Expected: rt_file_exists(llvm_native_out_path) is false
   - Expected: native_result.is_success() is false
   - Expected: rt_file_exists(native_out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("grouped backend helper imports resolve cleanly for a direct external caller")
val src_path = "/tmp/sml_driver_api_grouped_backend.spl"
val llvm_native_out_path = "/tmp/sml_driver_api_grouped_backend_llvm_native.bin"
val native_out_path = "/tmp/sml_driver_api_grouped_backend_native.bin"
val _vhdl_emit2 = aot_vhdl_file
write_file(src_path, "fn add(a: i32, b: i32) -> i32:\n    a + b")
delete_file(llvm_native_out_path)
delete_file(native_out_path)

val llvm_native_result = aot_llvm_native_file(src_path, llvm_native_out_path)
val native_result = aot_native_file_with_backend(src_path, native_out_path, "llvm-lib", false, 0)

expect(llvm_native_result.is_success()).to_equal(false)
expect(rt_file_exists(llvm_native_out_path)).to_equal(false)
expect(native_result.is_success()).to_equal(false)
expect(rt_file_exists(native_out_path)).to_equal(false)

delete_file(src_path)
delete_file(llvm_native_out_path)
delete_file(native_out_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/driver_api_external_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Driver API External Facade.
- Driver API External Facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `f50ca270dab2d7f5c65effb5a52e72532ae1b6074ca5a1a1bf034b1ac94c4d9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f50ca270dab2d7f5c65effb5a52e72532ae1b6074ca5a1a1bf034b1ac94c4d9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f50ca270dab2d7f5c65effb5a52e72532ae1b6074ca5a1a1bf034b1ac94c4d9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/driver_api_external_facade_spec.spl
mirror: doc/06_spec/03_system/compiler/driver_api_external_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/driver_api_external_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/driver_api_external_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/driver_api_external_facade_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compile_to_smf writes an smf artifact for a direct external caller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/driver_api_external_facade_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check_file returns success for a valid source file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/driver_api_external_facade_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_sdn_file returns success for a readable sdn file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
