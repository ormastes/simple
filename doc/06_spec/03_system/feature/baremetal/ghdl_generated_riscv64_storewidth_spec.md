# Ghdl Generated Riscv64 Storewidth Specification

> Tests covering Generated RV64 GHDL store width.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv64 Storewidth Specification

## Scenarios

### Generated RV64 GHDL store width

#### runner script exists and store-width smoke source is present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runner script exists and store-width smoke source is present
   - Expected: rt_file_exists(GENERATED_RUNNER) is true
   - Expected: rt_file_exists(GENERATED_STOREWIDTH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runner script exists and store-width smoke source is present")
expect(rt_file_exists(GENERATED_RUNNER)).to_equal(true)
expect(rt_file_exists(GENERATED_STOREWIDTH)).to_equal(true)
```

</details>

<details>
<summary>Advanced: runs a generated RV64 sb sh sw lane smoke program</summary>

#### runs a generated RV64 sb sh sw lane smoke program _(slow)_

- runs a generated RV64 sb sh sw lane smoke program
   - Expected: 1 equals `1`
   - Expected: 1 equals `1`
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs a generated RV64 sb sh sw lane smoke program")
if not runner_tools_available():
    expect(1).to_equal(1)
else:
    val result = rt_process_run_timeout("bash", [GENERATED_RUNNER, GENERATED_STOREWIDTH, "--timeout=30"], 120000)
    if result[2] == 2:
        expect(1).to_equal(1)
    else:
        val output = result[0] + result[1]
        expect(result[2]).to_equal(0)
        expect(output).to_contain("GENERATED_RV64_SMOKE: PASS")
        expect(output).to_contain("PASS_WORD: 42")
        expect(output).to_contain("FAIL_WORD: 0")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Generated RV64 GHDL store width.
- Generated RV64 GHDL store width

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

- Canonical SPipe generation for source `e8748a5ddf62ec4521e0785071c065b62303b1c08e29275dfb927019928c45f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8748a5ddf62ec4521e0785071c065b62303b1c08e29275dfb927019928c45f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8748a5ddf62ec4521e0785071c065b62303b1c08e29275dfb927019928c45f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runner script exists and store-width smoke source is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/ghdl_generated_riscv64_storewidth_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs a generated RV64 sb sh sw lane smoke program' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
