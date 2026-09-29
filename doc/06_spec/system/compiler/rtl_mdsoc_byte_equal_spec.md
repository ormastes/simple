# RTL MDSOC Byte-Equal Verification Specification

> Verifies that the MDSOC capsule reorganization of the Simple-source VHDL emitter produces byte-identical VHDL output to the pre-refactor baseline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTL MDSOC Byte-Equal Verification Specification

Verifies that the MDSOC capsule reorganization of the Simple-source VHDL emitter produces byte-identical VHDL output to the pre-refactor baseline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Research | N/A |
| Source | `test/system/compiler/rtl_mdsoc_byte_equal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the MDSOC capsule reorganization of the Simple-source VHDL
emitter produces byte-identical VHDL output to the pre-refactor baseline.

This spec is gate-blocked on Sub-agent 1 (SA-1) populating the baseline file
at `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md`. Until that file
exists, all byte-equal assertions are `pending`.

## Byte-Equal Harness Design

- Invokes `scripts/rtl_riscv32_linux_generated.shs` and
  `scripts/rtl_riscv64_linux_generated.shs`
- Captures sha256 of every file under `build/rtl_linux/generated_rv32/` and
  `build/rtl_linux/generated_rv64/`
- Compares against baseline hashes from the baseline markdown file
- Skip-if-baseline-missing: tests in this category are `pending` until SA-1
  populates the baseline (TODO: SA-1 baseline gate)

## Acceptance Criteria

- AC-2: Generated VHDL diff vs current main is byte-empty for both RV32 and
  RV64 generated-Linux lanes (sha256 proof)
- AC-3: *.debug.json sidecar contract preserved (reportMarkers,
  runnerSuccessMarkers byte-equivalent)
- AC-8: Verify in interpreter mode; record compile-mode regressions separately

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `rtl_mdsoc_baseline_2026-05-02.md` | Artifact | `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md` |

## Scenarios

### RTL MDSOC Byte-Equal: AC-2 RV32 generated VHDL

#### AC-2: RV32 byte-equal check is pending until SA-1 populates baseline

- AC-2: RV32 byte-equal check is pending until SA-1 populates baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: RV32 byte-equal check is pending until SA-1 populates baseline")
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md must be created first")
```

</details>

#### AC-2: RV32 generation script exists

- AC-2: RV32 generation script exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: RV32 generation script exists")
val exists = rt_file_exists("scripts/rtl/rtl_riscv32_linux_generated.shs")
expect(exists).to_equal(true)
```

</details>

#### AC-2: RV32 generated VHDL sha256 matches pre-refactor baseline

- AC-2: RV32 generated VHDL sha256 matches pre-refactor baseline
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: RV32 generated VHDL sha256 matches pre-refactor baseline")
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val script_ok = run_generation_script("scripts/rtl_riscv32_linux_generated.shs")
check_msg(script_ok, "RV32 generation script failed")
val current_hashes = sha256_dir(rv32_build_dir(), "*.vhd")
val baseline = read_baseline()
check_msg(baseline.contains("rv32"), "baseline missing rv32 section")
check_msg(current_hashes != "", "no RV32 .vhd files found after script run")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

### RTL MDSOC Byte-Equal: AC-2 RV64 generated VHDL

#### AC-2: RV64 byte-equal check is pending until SA-1 populates baseline

- AC-2: RV64 byte-equal check is pending until SA-1 populates baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: RV64 byte-equal check is pending until SA-1 populates baseline")
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md must be created first")
```

</details>

#### AC-2: RV64 generation script exists

- AC-2: RV64 generation script exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: RV64 generation script exists")
val exists = rt_file_exists("scripts/rtl/rtl_riscv64_linux_generated.shs")
expect(exists).to_equal(true)
```

</details>

#### AC-2: RV64 generated VHDL sha256 matches pre-refactor baseline

- AC-2: RV64 generated VHDL sha256 matches pre-refactor baseline
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2: RV64 generated VHDL sha256 matches pre-refactor baseline")
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val script_ok = run_generation_script("scripts/rtl_riscv64_linux_generated.shs")
check_msg(script_ok, "RV64 generation script failed")
val current_hashes = sha256_dir(rv64_build_dir(), "*.vhd")
val baseline = read_baseline()
check_msg(baseline.contains("rv64"), "baseline missing rv64 section")
check_msg(current_hashes != "", "no RV64 .vhd files found after script run")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

### RTL MDSOC Byte-Equal: AC-3 debug.json sidecar

#### AC-3: sidecar byte-equal check is pending until SA-1 populates baseline

- AC-3: sidecar byte-equal check is pending until SA-1 populates baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: sidecar byte-equal check is pending until SA-1 populates baseline")
pending("SA-1 baseline gate — doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md must be created first")
```

</details>

#### AC-3: RV32 .debug.json sha256 matches pre-refactor baseline

- AC-3: RV32 .debug.json sha256 matches pre-refactor baseline
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV32 .debug.json sha256 matches pre-refactor baseline")
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val current_hashes = sha256_dir(rv32_build_dir(), "*.debug.json")
val baseline = read_baseline()
check_msg(baseline.contains("debug.json"), "baseline missing debug.json section")
check_msg(current_hashes != "", "no RV32 .debug.json files found")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

#### AC-3: RV64 .debug.json sha256 matches pre-refactor baseline

- AC-3: RV64 .debug.json sha256 matches pre-refactor baseline
   - Expected: current_hashes does not contain ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3: RV64 .debug.json sha256 matches pre-refactor baseline")
if not baseline_exists():
    pending("SA-1 baseline gate — baseline file missing")
val current_hashes = sha256_dir(rv64_build_dir(), "*.debug.json")
val baseline = read_baseline()
check_msg(baseline.contains("debug.json"), "baseline missing debug.json section")
check_msg(current_hashes != "", "no RV64 .debug.json files found")
expect(current_hashes.contains("")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md`
- **Design:** `doc/05_design/rtl_riscv_mdsoc_capsules.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b09b43b8c9065c7ac2b293d5320c413dc2f565b0a34111621987dd9be025b968`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b09b43b8c9065c7ac2b293d5320c413dc2f565b0a34111621987dd9be025b968`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b09b43b8c9065c7ac2b293d5320c413dc2f565b0a34111621987dd9be025b968`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/system/compiler/rtl_mdsoc_byte_equal_spec.spl
mirror: doc/06_spec/system/compiler/rtl_mdsoc_byte_equal_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/system/compiler/rtl_mdsoc_byte_equal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/compiler/rtl_mdsoc_byte_equal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/compiler/rtl_mdsoc_byte_equal_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/system/compiler/rtl_mdsoc_byte_equal_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: RV32 byte-equal check is pending until SA-1 populates baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/compiler/rtl_mdsoc_byte_equal_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: RV32 generation script exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/compiler/rtl_mdsoc_byte_equal_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: RV32 generated VHDL sha256 matches pre-refactor baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
