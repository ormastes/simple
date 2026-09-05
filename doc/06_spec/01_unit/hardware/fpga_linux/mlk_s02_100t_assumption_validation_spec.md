# Mlk S02 100t Assumption Validation Specification

> Tests covering MLK-S02-100T assumption validation campaign.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mlk S02 100t Assumption Validation Specification

## Scenarios

### MLK-S02-100T assumption validation campaign

#### locks the launch plan to the assumption-only MLK lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- locks the launch plan to the assumption-only MLK lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locks the launch plan to the assumption-only MLK lane")
val script = read_text("scripts/mlk_s02_100t_assumption_validation.shs")
expect(script).to_contain("scripts/mlk_s02_100t_generated_linux.shs")
expect(script).to_contain("mlk_s02_100t_assumed_unverified.xdc")
expect(script).to_contain("--allow-assumed-board-top")
expect(script).to_contain("--allow-unsafe-assumed-bitstream")
expect(script).to_contain("ARCH_MODE=\"both\"")
expect(script).to_contain("rv32 rv64")
```

</details>

<details>
<summary>Advanced: records the staged matrix and assumption ledger for each arch</summary>

#### records the staged matrix and assumption ledger for each arch

- records the staged matrix and assumption ledger for each arch


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records the staged matrix and assumption ledger for each arch")
val script = read_text("scripts/mlk_s02_100t_assumption_validation.shs")
expect(script).to_contain("generated Linux behavioral gate")
expect(script).to_contain("assumption-only synth")
expect(script).to_contain("assumption-only place/route")
expect(script).to_contain("assumption-only bitstream")
expect(script).to_contain("hardware programming")
expect(script).to_contain("UART observation")
expect(script).to_contain("Linux launch attempt")
expect(script).to_contain("Assumption Ledger")
expect(script).to_contain("confirmed by toolchain only")
expect(script).to_contain("confirmed by programming only")
expect(script).to_contain("confirmed by UART/LED hardware behavior")
expect(script).to_contain("still unknown")
```

</details>


</details>

#### keeps linux launch gated behind staged artifacts and a boot delivery command

- keeps linux launch gated behind staged artifacts and a boot delivery command


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps linux launch gated behind staged artifacts and a boot delivery command")
val script = read_text("scripts/mlk_s02_100t_assumption_validation.shs")
expect(script).to_contain("boot delivery command not configured")
expect(script).to_contain("linux_stage_ready()")
expect(script).to_contain("staged_boot_artifact_path")
expect(script).to_contain("--prepare-only --skip-ghdl")
expect(script).to_contain("--skip-ghdl --skip-synth --skip-program")
expect(script).to_contain("assumption-only wrapper ties memory off and drives uart_tx idle-high; Linux boot proof is blocked")
expect(script).to_contain("if [ \"$linux_status\" = \"pass\" ]; then")
```

</details>

#### documents the assumption validation runner in the assumed profile guide

- documents the assumption validation runner in the assumed profile guide


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the assumption validation runner in the assumed profile guide")
val guide = read_text("doc/07_guide/hardware/mlk_s02_100t_assumed_profile.md")
expect(guide).to_contain("scripts/mlk_s02_100t_assumption_validation.shs")
expect(guide).to_contain("build/fpga/mlk_s02_100t/assumption_validation/")
expect(guide).to_contain("confirmed by UART/LED hardware behavior")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MLK-S02-100T assumption validation campaign.
- MLK-S02-100T assumption validation campaign

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `66964772aec5d79eef78ab4dceb255bb282eadd6fb0b39f686cb0dfaaf0ebe7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66964772aec5d79eef78ab4dceb255bb282eadd6fb0b39f686cb0dfaaf0ebe7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66964772aec5d79eef78ab4dceb255bb282eadd6fb0b39f686cb0dfaaf0ebe7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl
mirror: doc/06_spec/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locks the launch plan to the assumption-only MLK lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the staged matrix and assumption ledger for each arch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps linux launch gated behind staged artifacts and a boot delivery command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
