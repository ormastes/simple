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
| Updated | 2026-08-27 |
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

#### complete live evidence for capability ledger is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for capability ledger is admitted
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-001")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-001")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for capability ledger is admitted")
step_boot_target()
check_simpleos_capability_matrix("REQ-001", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for capability ledger is preserved</summary>

#### the selected boundary for capability ledger is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for capability ledger is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-001")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-001")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for capability ledger is preserved")
step_boot_target()
check_simpleos_capability_matrix("REQ-001", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for capability ledger is rejected</summary>

#### missing stale substituted or invalid evidence for capability ledger is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for capability ledger is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-001")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-001")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for capability ledger is rejected")
step_boot_target()
check_simpleos_capability_matrix("REQ-001", "rejection")
```

</details>


</details>

### REQ-019: canonical ownership and duplicate removal

#### complete live evidence for canonical ownership and duplicate removal is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for canonical ownership and duplicate removal is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-019")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-019")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for canonical ownership and duplicate removal is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-019", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for canonical ownership and duplicate removal is preserved</summary>

#### the selected boundary for canonical ownership and duplicate removal is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for canonical ownership and duplicate removal is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-019")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-019")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for canonical ownership and duplicate removal is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-019", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for canonical ownership and duplicate removal is rejected</summary>

#### missing stale substituted or invalid evidence for canonical ownership and duplicate removal is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for canonical ownership and duplicate removal is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-019")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-019")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for canonical ownership and duplicate removal is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-019", "rejection")
```

</details>


</details>

### REQ-020: evidence, manuals, and knowledge

#### complete live evidence for evidence, manuals, and knowledge is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for evidence, manuals, and knowledge is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-020")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-020")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for evidence, manuals, and knowledge is admitted")
step_boot_target()
check_simpleos_capability_matrix("REQ-020", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for evidence, manuals, and knowledge is preserved</summary>

#### the selected boundary for evidence, manuals, and knowledge is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for evidence, manuals, and knowledge is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-020")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-020")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for evidence, manuals, and knowledge is preserved")
step_boot_target()
check_simpleos_capability_matrix("REQ-020", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for evidence, manuals, and knowledge is rejected</summary>

#### missing stale substituted or invalid evidence for evidence, manuals, and knowledge is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for evidence, manuals, and knowledge is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-020")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-020")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for evidence, manuals, and knowledge is rejected")
step_boot_target()
check_simpleos_capability_matrix("REQ-020", "rejection")
```

</details>


</details>

### NFR-001: architecture evidence

#### complete live evidence for architecture evidence is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for architecture evidence is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-001")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-001")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for architecture evidence is admitted")
step_boot_target()
check_simpleos_capability_matrix("NFR-001", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for architecture evidence is preserved</summary>

#### the selected boundary for architecture evidence is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for architecture evidence is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-001")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-001")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for architecture evidence is preserved")
step_boot_target()
check_simpleos_capability_matrix("NFR-001", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for architecture evidence is rejected</summary>

#### missing stale substituted or invalid evidence for architecture evidence is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for architecture evidence is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-001")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-001")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for architecture evidence is rejected")
step_boot_target()
check_simpleos_capability_matrix("NFR-001", "rejection")
```

</details>


</details>

### NFR-007: parallel ownership safety

#### complete live evidence for parallel ownership safety is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for parallel ownership safety is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-007")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-007")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for parallel ownership safety is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-007", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for parallel ownership safety is preserved</summary>

#### the selected boundary for parallel ownership safety is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for parallel ownership safety is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-007")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-007")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for parallel ownership safety is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-007", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for parallel ownership safety is rejected</summary>

#### missing stale substituted or invalid evidence for parallel ownership safety is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for parallel ownership safety is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-007")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-007")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for parallel ownership safety is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-007", "rejection")
```

</details>


</details>

### NFR-008: duplication gate

#### complete live evidence for duplication gate is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for duplication gate is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-008")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-008")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for duplication gate is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-008", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for duplication gate is preserved</summary>

#### the selected boundary for duplication gate is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for duplication gate is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-008")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-008")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for duplication gate is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-008", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for duplication gate is rejected</summary>

#### missing stale substituted or invalid evidence for duplication gate is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for duplication gate is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-008")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-008")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for duplication gate is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-008", "rejection")
```

</details>


</details>

### NFR-009: coverage and stub prevention

#### complete live evidence for coverage and stub prevention is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for coverage and stub prevention is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-009")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-009")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for coverage and stub prevention is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-009", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for coverage and stub prevention is preserved</summary>

#### the selected boundary for coverage and stub prevention is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for coverage and stub prevention is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-009")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-009")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for coverage and stub prevention is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-009", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for coverage and stub prevention is rejected</summary>

#### missing stale substituted or invalid evidence for coverage and stub prevention is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for coverage and stub prevention is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-009")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-009")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for coverage and stub prevention is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-009", "rejection")
```

</details>


</details>

### NFR-012: evidence freshness

#### complete live evidence for evidence freshness is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for evidence freshness is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-012")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-012")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for evidence freshness is admitted")
step_boot_target()
check_simpleos_capability_matrix("NFR-012", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for evidence freshness is preserved</summary>

#### the selected boundary for evidence freshness is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for evidence freshness is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-012")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-012")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for evidence freshness is preserved")
step_boot_target()
check_simpleos_capability_matrix("NFR-012", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for evidence freshness is rejected</summary>

#### missing stale substituted or invalid evidence for evidence freshness is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for evidence freshness is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-012")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-012")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for evidence freshness is rejected")
step_boot_target()
check_simpleos_capability_matrix("NFR-012", "rejection")
```

</details>


</details>

### NFR-013: convergence guard

#### complete live evidence for convergence guard is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for convergence guard is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-013")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-013")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for convergence guard is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-013", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for convergence guard is preserved</summary>

#### the selected boundary for convergence guard is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for convergence guard is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-013")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-013")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for convergence guard is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-013", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for convergence guard is rejected</summary>

#### missing stale substituted or invalid evidence for convergence guard is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for convergence guard is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-013")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-013")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for convergence guard is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-013", "rejection")
```

</details>


</details>

### NFR-014: documentation quality

#### complete live evidence for documentation quality is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for documentation quality is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-014")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-014")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for documentation quality is admitted")
step_boot_target()
check_simpleos_capability_matrix("NFR-014", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for documentation quality is preserved</summary>

#### the selected boundary for documentation quality is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for documentation quality is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-014")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-014")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for documentation quality is preserved")
step_boot_target()
check_simpleos_capability_matrix("NFR-014", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for documentation quality is rejected</summary>

#### missing stale substituted or invalid evidence for documentation quality is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for documentation quality is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-014")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-014")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for documentation quality is rejected")
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

- Canonical SPipe generation for source `4b85aeabfcde87f0ffbbc44fbc522bf96729ac6dd15040feb12f3e786f3fa05f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b85aeabfcde87f0ffbbc44fbc522bf96729ac6dd15040feb12f3e786f3fa05f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b85aeabfcde87f0ffbbc44fbc522bf96729ac6dd15040feb12f3e786f3fa05f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
