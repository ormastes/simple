# Generated 2D native readback wrapper evidence

> Runs the Metal and ROCm/HIP generated-2D readback wrappers into isolated build-local evidence directories and asserts their deterministic `evidence.env` contracts. Linux hosts without Metal or ROCm are expected to fail closed with typed unavailable evidence; native host passes must prove submit plus readback availability and matching operation checksums.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated 2D native readback wrapper evidence

Runs the Metal and ROCm/HIP generated-2D readback wrappers into isolated build-local evidence directories and asserts their deterministic `evidence.env` contracts. Linux hosts without Metal or ROCm are expected to fail closed with typed unavailable evidence; native host passes must prove submit plus readback availability and matching operation checksums.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/check/generated_2d_native_readback_wrappers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the Metal and ROCm/HIP generated-2D readback wrappers into isolated
build-local evidence directories and asserts their deterministic `evidence.env`
contracts. Linux hosts without Metal or ROCm are expected to fail closed with
typed unavailable evidence; native host passes must prove submit plus readback
availability and matching operation checksums.

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/05_design/host_gpu_lane.md
**Report:** doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md

## Syntax

Run wrappers with isolated evidence directories:

```sh
BUILD_DIR=build/test-metal-generated-2d-readback \
REPORT_PATH=build/test-metal-generated-2d-readback/report.md \
sh scripts/check/check-metal-generated-2d-readback.shs

BUILD_DIR=build/test-rocm-generated-2d-readback \
REPORT_PATH=build/test-rocm-generated-2d-readback/report.md \
sh scripts/check/check-rocm-generated-2d-readback.shs
```

Each wrapper writes direct evidence keys such as:

```text
metal_generated_2d_readback_status=unavailable
metal_generated_2d_readback_readback_available=false
metal_generated_2d_readback_required_path='Metal source -> metallib -> MTLDevice -> compute pipeline -> command buffer/encoder -> submit -> wait -> buffer readback -> per-op checksums'
rocm_generated_2d_readback_status=unavailable
rocm_generated_2d_readback_readback_available=false
rocm_generated_2d_readback_required_path='HIP source -> HSACO -> ROCm loader -> device/module/kernel handles -> launch -> synchronize -> host readback -> per-op checksums'
```

## Examples

A native pass must report `status=pass`, `submit_attempted=true`, and
`readback_available=true`. Metal and ROCm/HIP report per-operation checksums for
`fill`, `copy`, `alpha`, and `scroll`; those must match their expected values.

## Acceptance

- Metal evidence includes runtime, tool, module, submit, readback, checksum,
  and operation keys.
- ROCm/HIP evidence includes loader, probe, module, submit, readback, checksum,
  and operation keys.
- Unavailable evidence must report `readback_available=false`.
- Pass evidence must prove submit/readback and matching checksums.

## Scenarios

### Generated 2D native readback wrappers

#### writes fail-closed Metal generated readback evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes fail-closed Metal generated readback evidence
   - Expected: submit equals `true`
   - Expected: readback equals `true`
   - Expected: _value_of(evidence, "metal_generated_2d_readback_fill_checksum") equals `_value_of(evidence, "metal_generated_2d_readback_fill_expected")`
   - Expected: _value_of(evidence, "metal_generated_2d_readback_copy_checksum") equals `_value_of(evidence, "metal_generated_2d_readback_copy_expected")`
   - Expected: _value_of(evidence, "metal_generated_2d_readback_alpha_checksum") equals `_value_of(evidence, "metal_generated_2d_readback_alpha_expected")`
   - Expected: _value_of(evidence, "metal_generated_2d_readback_scroll_checksum") equals `_value_of(evidence, "metal_generated_2d_readback_scroll_expected")`
   - Expected: status equals `unavailable`
   - Expected: readback equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes fail-closed Metal generated readback evidence")
val evidence = _run_wrapper("build/test-metal-generated-2d-readback", "scripts/check/check-metal-generated-2d-readback.shs")
expect(evidence).to_contain("metal_generated_2d_readback_status=")
expect(evidence).to_contain("metal_generated_2d_readback_reason=")
expect(evidence).to_contain("metal_generated_2d_readback_runtime_present=")
expect(evidence).to_contain("metal_generated_2d_readback_metal_tool_present=")
expect(evidence).to_contain("metal_generated_2d_readback_metallib_tool_present=")
expect(evidence).to_contain("metal_generated_2d_readback_module_verified=")
expect(evidence).to_contain("metal_generated_2d_readback_submit_attempted=")
expect(evidence).to_contain("metal_generated_2d_readback_readback_available=")
expect(evidence).to_contain("metal_generated_2d_readback_ops=fill,copy,alpha,scroll")
expect(evidence).to_contain("metal_generated_2d_readback_required_path='Metal source -> metallib -> MTLDevice -> compute pipeline -> command buffer/encoder -> submit -> wait -> buffer readback -> per-op checksums'")

val status = _value_of(evidence, "metal_generated_2d_readback_status")
val readback = _value_of(evidence, "metal_generated_2d_readback_readback_available")
val submit = _value_of(evidence, "metal_generated_2d_readback_submit_attempted")
val reason = _value_of(evidence, "metal_generated_2d_readback_reason")
if status == "pass":
    expect(submit).to_equal("true")
    expect(readback).to_equal("true")
    expect(_value_of(evidence, "metal_generated_2d_readback_fill_checksum")).to_equal(_value_of(evidence, "metal_generated_2d_readback_fill_expected"))
    expect(_value_of(evidence, "metal_generated_2d_readback_copy_checksum")).to_equal(_value_of(evidence, "metal_generated_2d_readback_copy_expected"))
    expect(_value_of(evidence, "metal_generated_2d_readback_alpha_checksum")).to_equal(_value_of(evidence, "metal_generated_2d_readback_alpha_expected"))
    expect(_value_of(evidence, "metal_generated_2d_readback_scroll_checksum")).to_equal(_value_of(evidence, "metal_generated_2d_readback_scroll_expected"))
else:
    expect(status).to_equal("unavailable")
    expect(readback).to_equal("false")
    expect(reason.len()).to_be_greater_than(0)
```

</details>

#### rejects forged Metal harness pass with mismatched per-op checksums

- rejects forged Metal harness pass with mismatched per-op checksums
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects forged Metal harness pass with mismatched per-op checksums")
val rows = "status=pass\\nfill_checksum=1\\nfill_expected=1\\ncopy_checksum=2\\ncopy_expected=2\\nalpha_checksum=3\\nalpha_expected=999\\nscroll_checksum=4\\nscroll_expected=4\\nsubmit_attempted=true\\nreadback_available=true\\n"
val command = _fake_metal_harness_command("build/test-metal-generated-2d-readback-forged", rows)
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-metal-generated-2d-readback-forged/evidence.env")
expect(evidence).to_contain("metal_generated_2d_readback_status=fail")
expect(evidence).to_contain("metal_generated_2d_readback_reason=alpha-checksum-mismatch")
expect(evidence).to_contain("metal_generated_2d_readback_expected_checksum=1006")
expect(evidence).to_contain("metal_generated_2d_readback_actual_checksum=10")
expect(evidence).to_contain("metal_generated_2d_readback_alpha_checksum=3")
expect(evidence).to_contain("metal_generated_2d_readback_alpha_expected=999")
```

</details>

#### accepts Metal harness pass only after matching nonzero per-op checksums

- accepts Metal harness pass only after matching nonzero per-op checksums
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts Metal harness pass only after matching nonzero per-op checksums")
val rows = "status=pass\\nfill_checksum=1\\nfill_expected=1\\ncopy_checksum=2\\ncopy_expected=2\\nalpha_checksum=3\\nalpha_expected=3\\nscroll_checksum=4\\nscroll_expected=4\\nsubmit_attempted=true\\nreadback_available=true\\n"
val command = _fake_metal_harness_command("build/test-metal-generated-2d-readback-harness-pass", rows)
val (_stdout, _stderr, code) = rt_process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = rt_file_read_text("build/test-metal-generated-2d-readback-harness-pass/evidence.env")
expect(evidence).to_contain("metal_generated_2d_readback_status=pass")
expect(evidence).to_contain("metal_generated_2d_readback_reason=gpu-readback-verified")
expect(evidence).to_contain("metal_generated_2d_readback_expected_checksum=10")
expect(evidence).to_contain("metal_generated_2d_readback_actual_checksum=10")
expect(evidence).to_contain("metal_generated_2d_readback_submit_attempted=true")
expect(evidence).to_contain("metal_generated_2d_readback_readback_available=true")
```

</details>

#### writes fail-closed ROCm generated readback evidence

- writes fail-closed ROCm generated readback evidence
   - Expected: submit equals `true`
   - Expected: readback equals `true`
   - Expected: _value_of(evidence, "rocm_generated_2d_readback_fill_checksum") equals `_value_of(evidence, "rocm_generated_2d_readback_fill_expected")`
   - Expected: _value_of(evidence, "rocm_generated_2d_readback_copy_checksum") equals `_value_of(evidence, "rocm_generated_2d_readback_copy_expected")`
   - Expected: _value_of(evidence, "rocm_generated_2d_readback_alpha_checksum") equals `_value_of(evidence, "rocm_generated_2d_readback_alpha_expected")`
   - Expected: _value_of(evidence, "rocm_generated_2d_readback_scroll_checksum") equals `_value_of(evidence, "rocm_generated_2d_readback_scroll_expected")`
   - Expected: status equals `unavailable`
   - Expected: readback equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes fail-closed ROCm generated readback evidence")
val evidence = _run_wrapper("build/test-rocm-generated-2d-readback", "scripts/check/check-rocm-generated-2d-readback.shs")
expect(evidence).to_contain("rocm_generated_2d_readback_status=")
expect(evidence).to_contain("rocm_generated_2d_readback_reason=")
expect(evidence).to_contain("rocm_generated_2d_readback_loader_present=")
expect(evidence).to_contain("rocm_generated_2d_readback_probe_tool_present=")
expect(evidence).to_contain("rocm_generated_2d_readback_module_verified=")
expect(evidence).to_contain("rocm_generated_2d_readback_submit_attempted=")
expect(evidence).to_contain("rocm_generated_2d_readback_readback_available=")
expect(evidence).to_contain("rocm_generated_2d_readback_ops=fill,copy,alpha,scroll")
expect(evidence).to_contain("rocm_generated_2d_readback_required_path='HIP source -> HSACO -> ROCm loader -> device/module/kernel handles -> launch -> synchronize -> host readback -> per-op checksums'")

val status = _value_of(evidence, "rocm_generated_2d_readback_status")
val readback = _value_of(evidence, "rocm_generated_2d_readback_readback_available")
val submit = _value_of(evidence, "rocm_generated_2d_readback_submit_attempted")
val reason = _value_of(evidence, "rocm_generated_2d_readback_reason")
if status == "pass":
    expect(submit).to_equal("true")
    expect(readback).to_equal("true")
    expect(_value_of(evidence, "rocm_generated_2d_readback_fill_checksum")).to_equal(_value_of(evidence, "rocm_generated_2d_readback_fill_expected"))
    expect(_value_of(evidence, "rocm_generated_2d_readback_copy_checksum")).to_equal(_value_of(evidence, "rocm_generated_2d_readback_copy_expected"))
    expect(_value_of(evidence, "rocm_generated_2d_readback_alpha_checksum")).to_equal(_value_of(evidence, "rocm_generated_2d_readback_alpha_expected"))
    expect(_value_of(evidence, "rocm_generated_2d_readback_scroll_checksum")).to_equal(_value_of(evidence, "rocm_generated_2d_readback_scroll_expected"))
else:
    expect(status).to_equal("unavailable")
    expect(readback).to_equal("false")
    expect(reason.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/host_gpu_lane.md`
- **Plan:** `doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md`
- **Design:** `doc/05_design/host_gpu_lane.md`
- **Research:** `doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee20740c56fab9b0e997ca6a051acda1ae8cc7d78d9e9cbc8d5f37b0b145a4c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee20740c56fab9b0e997ca6a051acda1ae8cc7d78d9e9cbc8d5f37b0b145a4c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee20740c56fab9b0e997ca6a051acda1ae8cc7d78d9e9cbc8d5f37b0b145a4c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/generated_2d_native_readback_wrappers_spec.spl
mirror: doc/06_spec/03_system/check/generated_2d_native_readback_wrappers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/generated_2d_native_readback_wrappers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/generated_2d_native_readback_wrappers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/generated_2d_native_readback_wrappers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/generated_2d_native_readback_wrappers_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes fail-closed Metal generated readback evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/generated_2d_native_readback_wrappers_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects forged Metal harness pass with mismatched per-op checksums' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/generated_2d_native_readback_wrappers_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts Metal harness pass only after matching nonzero per-op checksums' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
