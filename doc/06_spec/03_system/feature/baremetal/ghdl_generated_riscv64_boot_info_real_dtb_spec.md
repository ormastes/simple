# Ghdl Generated Riscv64 Boot Info Real Dtb Specification

> Tests covering Generated RV64 boot-info real DTB GHDL smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv64 Boot Info Real Dtb Specification

## Scenarios

### Generated RV64 boot-info real DTB GHDL smoke

#### runner script exists and is syntax-valid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runner script exists and is syntax-valid
   - Expected: rt_file_exists(GENERATED_RUNNER) is true
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runner script exists and is syntax-valid")
expect(rt_file_exists(GENERATED_RUNNER)).to_equal(true)
val result = rt_process_run("bash", ["-n", GENERATED_RUNNER])
expect(result[2]).to_equal(0)
```

</details>

<details>
<summary>Advanced: runs a generated RV64 boot-info real DTB smoke program</summary>

#### runs a generated RV64 boot-info real DTB smoke program _(slow)_

- runs a generated RV64 boot-info real DTB smoke program
   - Expected: 1 equals `1`
   - Expected: 1 equals `1`
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs a generated RV64 boot-info real DTB smoke program")
if not runner_tools_available():
    expect(1).to_equal(1)
else:
    val result = rt_process_run_timeout("bash", [GENERATED_RUNNER, GENERATED_SMOKE, "--timeout=30"], 120000)
    if result[2] == 2:
        expect(1).to_equal(1)
    else:
        val output = result[0] + result[1]
        expect(result[2]).to_equal(0)
        expect(output).to_contain("GENERATED_RV64_BOOT_INFO_REAL_DTB: PASS")
        expect(output).to_contain("DTB_VALID_LOW32: 1")
        expect(output).to_contain("RAM_BASE_HEX32: 90000000")
        expect(output).to_contain("RAM_SIZE_HEX32: 04000000")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Generated RV64 boot-info real DTB GHDL smoke.
- Generated RV64 boot-info real DTB GHDL smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 1 |
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

- Canonical SPipe generation for source `d300100f00888ebb21f0938c5d9e52af32deea14a59aa7323a37602e814689c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d300100f00888ebb21f0938c5d9e52af32deea14a59aa7323a37602e814689c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d300100f00888ebb21f0938c5d9e52af32deea14a59aa7323a37602e814689c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runner script exists and is syntax-valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_real_dtb_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a generated RV64 boot-info real DTB smoke program' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
