# FPGA Linux riscv_fpga_linux.spl Split Specification

> Verifies that the 4547-line `riscv_fpga_linux.spl` is split into three specialized capsule files plus a thin re-export facade, that the facade preserves the original public API, and that line-count budgets are respected.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FPGA Linux riscv_fpga_linux.spl Split Specification

Verifies that the 4547-line `riscv_fpga_linux.spl` is split into three specialized capsule files plus a thin re-export facade, that the facade preserves the original public API, and that line-count budgets are respected.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Source | `test/03_system/compiler/fpga_linux_split_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the 4547-line `riscv_fpga_linux.spl` is split into three
specialized capsule files plus a thin re-export facade, that the facade
preserves the original public API, and that line-count budgets are respected.

## Split Design (Phase 3 D-2)

- `fpga_linux_orchestrator.spl` — Control capsule: lane runner, board structs,
  bundle generation (budget: < 900 lines)
- `fpga_linux_data.spl` — Data capsule: VHDL-emission methods (budget: < 2700 lines)
  NOTE: Phase 3 sizing estimated ~2855 lines for data — budget < 2700 may require
  additional split in Phase 5. Phase 5 SA-3 must resolve and record any deviation.
- `fpga_linux_manifest.spl` — Metadata capsule: debug sidecar JSON emission
  (budget: < 200 lines)
- `riscv_fpga_linux.spl` — Thin re-export facade (budget: < 30 lines)

## Public API Preservation (AC-1, AC-6)

The re-export facade must preserve:
- `RiscvFpgaLane`
- `FpgaPrepareManifest`
- `XilinxBoardProfile`

These are the canonical public symbols. Any probe that imports them from
`hardware.fpga_linux.riscv_fpga_linux` must resolve correctly.

## Acceptance Criteria

- AC-1: Physical split into named MDSOC capsules
- AC-6: Existing spec `pure_simple_vhdl_source_of_truth_spec.spl` must pass
  (probes that import riscv_fpga_linux symbols keep working)

TDD-red: split files do not exist before Phase 5 SA-3 runs.

## Scenarios

### FPGA Linux Split: file existence (AC-1)

#### AC-1: fpga_linux_orchestrator.spl exists

- AC-1: fpga_linux_orchestrator.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_orchestrator.spl exists")
val path = fpga_orch_path()
val exists = rt_file_exists(path)
check_msg(exists, "SA-3 not run yet — file missing: " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-1: fpga_linux_data.spl exists

- AC-1: fpga_linux_data.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_data.spl exists")
val path = fpga_data_path()
val exists = rt_file_exists(path)
check_msg(exists, "SA-3 not run yet — file missing: " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-1: fpga_linux_manifest.spl exists

- AC-1: fpga_linux_manifest.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_manifest.spl exists")
val path = fpga_manifest_path()
val exists = rt_file_exists(path)
check_msg(exists, "SA-3 not run yet — file missing: " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl (facade) still exists

- AC-1: riscv_fpga_linux.spl (facade) still exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl (facade) still exists")
val path = fpga_facade_path()
val exists = rt_file_exists(path)
expect(exists).to_equal(true)
```

</details>

### FPGA Linux Split: line-count budgets (AC-1)

#### AC-1: fpga_linux_orchestrator.spl is under 900 lines

- AC-1: fpga_linux_orchestrator.spl is under 900 lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_orchestrator.spl is under 900 lines")
val path = fpga_orch_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val lines = file_line_count(path)
check_msg(lines < 900, "orchestrator line count " + lines.to_text() + " exceeds budget of 900")
expect(lines).to_be_less_than(900)
```

</details>

#### AC-1: fpga_linux_data.spl is under 2700 lines

- AC-1: fpga_linux_data.spl is under 2700 lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_data.spl is under 2700 lines")
val path = fpga_data_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val lines = file_line_count(path)
check_msg(lines < 2700, "data line count " + lines.to_text() + " exceeds budget of 2700 (Phase 3 estimated 2855 — SA-3 must resolve)")
expect(lines).to_be_less_than(2700)
```

</details>

#### AC-1: fpga_linux_manifest.spl is under 200 lines

- AC-1: fpga_linux_manifest.spl is under 200 lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_manifest.spl is under 200 lines")
val path = fpga_manifest_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val lines = file_line_count(path)
check_msg(lines < 200, "manifest line count " + lines.to_text() + " exceeds budget of 200")
expect(lines).to_be_less_than(200)
```

</details>

### FPGA Linux Split: re-export facade preserves public API (AC-1, AC-6)

#### AC-1: riscv_fpga_linux.spl re-exports RiscvFpgaLane

- AC-1: riscv_fpga_linux.spl re-exports RiscvFpgaLane
   - Expected: has_symbol is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl re-exports RiscvFpgaLane")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "facade file not found: " + path)
val content = read_file(path)
val has_symbol = content.contains("RiscvFpgaLane")
expect(has_symbol).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl re-exports FpgaPrepareManifest

- AC-1: riscv_fpga_linux.spl re-exports FpgaPrepareManifest
   - Expected: has_symbol is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl re-exports FpgaPrepareManifest")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "facade file not found: " + path)
val content = read_file(path)
val has_symbol = content.contains("FpgaPrepareManifest")
expect(has_symbol).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl re-exports XilinxBoardProfile

- AC-1: riscv_fpga_linux.spl re-exports XilinxBoardProfile
   - Expected: has_symbol is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl re-exports XilinxBoardProfile")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "facade file not found: " + path)
val content = read_file(path)
val has_symbol = content.contains("XilinxBoardProfile")
expect(has_symbol).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl facade imports fpga_linux_orchestrator

- AC-1: riscv_fpga_linux.spl facade imports fpga_linux_orchestrator
   - Expected: has_import is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl facade imports fpga_linux_orchestrator")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "facade file not found: " + path)
val content = read_file(path)
val has_import = content.contains("fpga_linux_orchestrator")
expect(has_import).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl facade imports fpga_linux_data

- AC-1: riscv_fpga_linux.spl facade imports fpga_linux_data
   - Expected: has_import is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl facade imports fpga_linux_data")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "facade file not found: " + path)
val content = read_file(path)
val has_import = content.contains("fpga_linux_data")
expect(has_import).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl facade imports fpga_linux_manifest

- AC-1: riscv_fpga_linux.spl facade imports fpga_linux_manifest
   - Expected: has_import is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl facade imports fpga_linux_manifest")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "facade file not found: " + path)
val content = read_file(path)
val has_import = content.contains("fpga_linux_manifest")
expect(has_import).to_equal(true)
```

</details>

### FPGA Linux Split: smoke-script compatibility (AC-7)

#### AC-7: rtl_riscv32_linux_generated.shs script exists

- AC-7: rtl_riscv32_linux_generated.shs script exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: rtl_riscv32_linux_generated.shs script exists")
val path = rv32_script_path()
val exists = rt_file_exists(path)
expect(exists).to_equal(true)
```

</details>

#### AC-7: rtl_riscv64_linux_generated.shs script exists

- AC-7: rtl_riscv64_linux_generated.shs script exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: rtl_riscv64_linux_generated.shs script exists")
val path = rv64_script_path()
val exists = rt_file_exists(path)
expect(exists).to_equal(true)
```

</details>

#### AC-7: split files not absent when smoke scripts are invoked

- AC-7: split files not absent when smoke scripts are invoked
   - Expected: orch_ok is true
   - Expected: data_ok is true
   - Expected: manifest_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: split files not absent when smoke scripts are invoked")
# After SA-3 runs, the split files must be present for scripts to work.
# This test confirms the three capsule files exist as a precondition.
val orch_ok = rt_file_exists(fpga_orch_path())
val data_ok = rt_file_exists(fpga_data_path())
val manifest_ok = rt_file_exists(fpga_manifest_path())
check_msg(orch_ok, "orchestrator missing — smoke scripts will fail")
check_msg(data_ok, "data module missing — smoke scripts will fail")
check_msg(manifest_ok, "manifest module missing — smoke scripts will fail")
expect(orch_ok).to_equal(true)
expect(data_ok).to_equal(true)
expect(manifest_ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md`
- **Design:** `doc/05_design/rtl_riscv_mdsoc_capsules.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e8d55dab37180562fc29eb48b6a7b9c1892c7e5a65c30bde88a8b2bbf87fe4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e8d55dab37180562fc29eb48b6a7b9c1892c7e5a65c30bde88a8b2bbf87fe4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e8d55dab37180562fc29eb48b6a7b9c1892c7e5a65c30bde88a8b2bbf87fe4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/fpga_linux_split_spec.spl
mirror: doc/06_spec/03_system/compiler/fpga_linux_split_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/fpga_linux_split_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/fpga_linux_split_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/fpga_linux_split_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: fpga_linux_orchestrator.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/fpga_linux_split_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: fpga_linux_data.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/fpga_linux_split_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: fpga_linux_manifest.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
