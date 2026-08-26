# Capability ledger, ownership, and evidence manual

> Defines fail-closed acceptance for ledger truth, canonical ownership, three environment classes, freshness, duplication, stubs, convergence, and manual quality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability ledger, ownership, and evidence manual

Defines fail-closed acceptance for ledger truth, canonical ownership, three environment classes, freshness, duplication, stubs, convergence, and manual quality.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defines fail-closed acceptance for ledger truth, canonical ownership, three environment classes, freshness, duplication, stubs, convergence, and manual quality.

This is an explicit BLOCKED traceability spec. Each checker validates a
structurally complete blocked candidate through the production capability-ledger
owner and reports its executable owner, exact expected receipt, and resume
command. A row cannot pass until that receipt is produced and admitted.

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `` | TUI capture | `build/test-artifacts/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec/` |

## Scenarios

### REQ-001: capability ledger

#### should accept complete live evidence for capability ledger

- should accept complete live evidence for capability ledger
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for capability ledger")
step_boot_target()
check_simpleos_capability_matrix("REQ-001", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for capability ledger</summary>

#### should preserve the selected boundary for capability ledger

- should preserve the selected boundary for capability ledger


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for capability ledger")
step_boot_target()
check_simpleos_capability_matrix("REQ-001", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for capability ledger</summary>

#### should reject missing stale substituted or invalid evidence for capability ledger

- should reject missing stale substituted or invalid evidence for capability ledger


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for capability ledger")
step_boot_target()
check_simpleos_capability_matrix("REQ-001", "rejection")
```

</details>


</details>

### REQ-019: canonical ownership and duplicate removal

#### should accept complete live evidence for canonical ownership and duplicate removal

- should accept complete live evidence for canonical ownership and duplicate removal
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for canonical ownership and duplicate removal")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-019", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for canonical ownership and duplicate removal</summary>

#### should preserve the selected boundary for canonical ownership and duplicate removal

- should preserve the selected boundary for canonical ownership and duplicate removal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for canonical ownership and duplicate removal")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-019", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for canonical ownership and duplicate removal</summary>

#### should reject missing stale substituted or invalid evidence for canonical ownership and duplicate removal

- should reject missing stale substituted or invalid evidence for canonical ownership and duplicate removal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for canonical ownership and duplicate removal")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-019", "rejection")
```

</details>


</details>

### REQ-020: evidence, manuals, and knowledge

#### should accept complete live evidence for evidence, manuals, and knowledge

- should accept complete live evidence for evidence, manuals, and knowledge
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for evidence, manuals, and knowledge")
step_boot_target()
check_simpleos_capability_matrix("REQ-020", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for evidence, manuals, and knowledge</summary>

#### should preserve the selected boundary for evidence, manuals, and knowledge

- should preserve the selected boundary for evidence, manuals, and knowledge


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for evidence, manuals, and knowledge")
step_boot_target()
check_simpleos_capability_matrix("REQ-020", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for evidence, manuals, and knowledge</summary>

#### should reject missing stale substituted or invalid evidence for evidence, manuals, and knowledge

- should reject missing stale substituted or invalid evidence for evidence, manuals, and knowledge


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for evidence, manuals, and knowledge")
step_boot_target()
check_simpleos_capability_matrix("REQ-020", "rejection")
```

</details>


</details>

### NFR-001: architecture evidence

#### should accept complete live evidence for architecture evidence

- should accept complete live evidence for architecture evidence
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for architecture evidence")
step_boot_target()
check_simpleos_capability_matrix("NFR-001", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for architecture evidence</summary>

#### should preserve the selected boundary for architecture evidence

- should preserve the selected boundary for architecture evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for architecture evidence")
step_boot_target()
check_simpleos_capability_matrix("NFR-001", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for architecture evidence</summary>

#### should reject missing stale substituted or invalid evidence for architecture evidence

- should reject missing stale substituted or invalid evidence for architecture evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for architecture evidence")
step_boot_target()
check_simpleos_capability_matrix("NFR-001", "rejection")
```

</details>


</details>

### NFR-007: parallel ownership safety

#### should accept complete live evidence for parallel ownership safety

- should accept complete live evidence for parallel ownership safety
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for parallel ownership safety")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-007", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for parallel ownership safety</summary>

#### should preserve the selected boundary for parallel ownership safety

- should preserve the selected boundary for parallel ownership safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for parallel ownership safety")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-007", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for parallel ownership safety</summary>

#### should reject missing stale substituted or invalid evidence for parallel ownership safety

- should reject missing stale substituted or invalid evidence for parallel ownership safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for parallel ownership safety")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-007", "rejection")
```

</details>


</details>

### NFR-008: duplication gate

#### should accept complete live evidence for duplication gate

- should accept complete live evidence for duplication gate
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for duplication gate")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-008", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for duplication gate</summary>

#### should preserve the selected boundary for duplication gate

- should preserve the selected boundary for duplication gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for duplication gate")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-008", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for duplication gate</summary>

#### should reject missing stale substituted or invalid evidence for duplication gate

- should reject missing stale substituted or invalid evidence for duplication gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for duplication gate")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-008", "rejection")
```

</details>


</details>

### NFR-009: coverage and stub prevention

#### should accept complete live evidence for coverage and stub prevention

- should accept complete live evidence for coverage and stub prevention
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for coverage and stub prevention")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-009", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for coverage and stub prevention</summary>

#### should preserve the selected boundary for coverage and stub prevention

- should preserve the selected boundary for coverage and stub prevention


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for coverage and stub prevention")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-009", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for coverage and stub prevention</summary>

#### should reject missing stale substituted or invalid evidence for coverage and stub prevention

- should reject missing stale substituted or invalid evidence for coverage and stub prevention


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for coverage and stub prevention")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-009", "rejection")
```

</details>


</details>

### NFR-012: evidence freshness

#### should accept complete live evidence for evidence freshness

- should accept complete live evidence for evidence freshness
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for evidence freshness")
step_boot_target()
check_simpleos_capability_matrix("NFR-012", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for evidence freshness</summary>

#### should preserve the selected boundary for evidence freshness

- should preserve the selected boundary for evidence freshness


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for evidence freshness")
step_boot_target()
check_simpleos_capability_matrix("NFR-012", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for evidence freshness</summary>

#### should reject missing stale substituted or invalid evidence for evidence freshness

- should reject missing stale substituted or invalid evidence for evidence freshness


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for evidence freshness")
step_boot_target()
check_simpleos_capability_matrix("NFR-012", "rejection")
```

</details>


</details>

### NFR-013: convergence guard

#### should accept complete live evidence for convergence guard

- should accept complete live evidence for convergence guard
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for convergence guard")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-013", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for convergence guard</summary>

#### should preserve the selected boundary for convergence guard

- should preserve the selected boundary for convergence guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for convergence guard")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-013", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for convergence guard</summary>

#### should reject missing stale substituted or invalid evidence for convergence guard

- should reject missing stale substituted or invalid evidence for convergence guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for convergence guard")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-013", "rejection")
```

</details>


</details>

### NFR-014: documentation quality

#### should accept complete live evidence for documentation quality

- should accept complete live evidence for documentation quality
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for documentation quality")
step_boot_target()
check_simpleos_capability_matrix("NFR-014", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for documentation quality</summary>

#### should preserve the selected boundary for documentation quality

- should preserve the selected boundary for documentation quality


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for documentation quality")
step_boot_target()
check_simpleos_capability_matrix("NFR-014", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for documentation quality</summary>

#### should reject missing stale substituted or invalid evidence for documentation quality

- should reject missing stale substituted or invalid evidence for documentation quality


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for documentation quality")
step_boot_target()
check_simpleos_capability_matrix("NFR-014", "rejection")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-019`
- `REQ-020`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c1892fc8e9291c064dc9e51a606557e846b7b8c4c8f885c0c69c77b9a84d59f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c1892fc8e9291c064dc9e51a606557e846b7b8c4c8f885c0c69c77b9a84d59f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c1892fc8e9291c064dc9e51a606557e846b7b8c4c8f885c0c69c77b9a84d59f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for capability ledger' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept complete live evidence for capability ledger' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for capability ledger' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the selected boundary for capability ledger' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for capability ledger' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing stale substituted or invalid evidence for capability ledger' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for canonical ownership and duplicate removal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for canonical ownership and duplicate removal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for canonical ownership and duplicate removal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
