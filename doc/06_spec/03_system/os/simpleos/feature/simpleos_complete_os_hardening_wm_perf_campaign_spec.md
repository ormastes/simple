# Window manager and production campaigns

> Defines fail-closed live acceptance for canonical WM interaction/readback, observability, strict performance, fuzz, soak, and lifecycle bounds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window manager and production campaigns

Defines fail-closed live acceptance for canonical WM interaction/readback, observability, strict performance, fuzz, soak, and lifecycle bounds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Defines fail-closed live acceptance for canonical WM interaction/readback, observability, strict performance, fuzz, soak, and lifecycle bounds.

This is an explicit BLOCKED traceability spec. Each checker validates a
structurally complete blocked candidate through the production capability-ledger
owner and reports its executable owner, exact expected receipt, and resume
command. A row cannot pass until that receipt is produced and admitted.

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Screenshots | 1 |

### Screenshots

| Item | Kind | Path |
|------|------|------|
| `` | Screenshot | `doc/06_spec/image/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec/` |

## Scenarios

### REQ-017: production SimpleOS window manager

#### complete live evidence for production SimpleOS window manager is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for production SimpleOS window manager is admitted
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-017")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-017")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for production SimpleOS window manager is admitted")
step_exercise_window_manager()
check_simpleos_wm("REQ-017", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for production SimpleOS window manager is preserved</summary>

#### the selected boundary for production SimpleOS window manager is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for production SimpleOS window manager is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-017")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-017")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for production SimpleOS window manager is preserved")
step_exercise_window_manager()
check_simpleos_wm("REQ-017", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for production SimpleOS window manager is rejected</summary>

#### missing stale substituted or invalid evidence for production SimpleOS window manager is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for production SimpleOS window manager is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-017")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-017")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for production SimpleOS window manager is rejected")
step_exercise_window_manager()
check_simpleos_wm("REQ-017", "rejection")
```

</details>


</details>

### REQ-018: observability and performance ownership

#### complete live evidence for observability and performance ownership is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for observability and performance ownership is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-018")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-018")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for observability and performance ownership is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-018", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for observability and performance ownership is preserved</summary>

#### the selected boundary for observability and performance ownership is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for observability and performance ownership is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-018")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-018")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for observability and performance ownership is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-018", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for observability and performance ownership is rejected</summary>

#### missing stale substituted or invalid evidence for observability and performance ownership is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for observability and performance ownership is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("REQ-018")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("REQ-018")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for observability and performance ownership is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-018", "rejection")
```

</details>


</details>

### NFR-002: strict performance budgets

#### complete live evidence for strict performance budgets is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for strict performance budgets is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-002")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-002")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for strict performance budgets is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-002", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for strict performance budgets is preserved</summary>

#### the selected boundary for strict performance budgets is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for strict performance budgets is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-002")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-002")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for strict performance budgets is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-002", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for strict performance budgets is rejected</summary>

#### missing stale substituted or invalid evidence for strict performance budgets is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for strict performance budgets is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-002")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-002")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for strict performance budgets is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-002", "rejection")
```

</details>


</details>

### NFR-003: reproducible measurement

#### complete live evidence for reproducible measurement is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for reproducible measurement is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-003")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-003")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for reproducible measurement is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-003", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for reproducible measurement is preserved</summary>

#### the selected boundary for reproducible measurement is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for reproducible measurement is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-003")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-003")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for reproducible measurement is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-003", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for reproducible measurement is rejected</summary>

#### missing stale substituted or invalid evidence for reproducible measurement is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for reproducible measurement is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-003")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-003")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for reproducible measurement is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-003", "rejection")
```

</details>


</details>

### NFR-004: mission-critical robustness

#### complete live evidence for mission-critical robustness is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for mission-critical robustness is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-004")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-004")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for mission-critical robustness is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-004", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for mission-critical robustness is preserved</summary>

#### the selected boundary for mission-critical robustness is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for mission-critical robustness is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-004")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-004")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for mission-critical robustness is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-004", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for mission-critical robustness is rejected</summary>

#### missing stale substituted or invalid evidence for mission-critical robustness is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for mission-critical robustness is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-004")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-004")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for mission-critical robustness is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-004", "rejection")
```

</details>


</details>

### NFR-005: static core and dynamic application bounds

#### complete live evidence for static core and dynamic application bounds is admitted

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- complete live evidence for static core and dynamic application bounds is admitted
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-005")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-005")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("complete live evidence for static core and dynamic application bounds is admitted")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-005", "happy")
```

</details>

<details>
<summary>Advanced: the selected boundary for static core and dynamic application bounds is preserved</summary>

#### the selected boundary for static core and dynamic application bounds is preserved

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- the selected boundary for static core and dynamic application bounds is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-005")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-005")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("the selected boundary for static core and dynamic application bounds is preserved")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-005", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: missing stale substituted or invalid evidence for static core and dynamic application bounds is rejected</summary>

#### missing stale substituted or invalid evidence for static core and dynamic application bounds is rejected

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- missing stale substituted or invalid evidence for static core and dynamic application bounds is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
expect(simpleos_evidence_owner("NFR-005")).to_start_with("test/")  # oracle: the requirement is bound to a real acceptance-owner spec
expect(simpleos_evidence_owner("NFR-005")).to_end_with("_spec.spl")  # oracle: the owner is a spec file
step("missing stale substituted or invalid evidence for static core and dynamic application bounds is rejected")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-005", "rejection")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-017`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0fbd74aa43a76fda511f0ce74a94a5d495541a2f9461221db6548e9d33dd0214`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0fbd74aa43a76fda511f0ce74a94a5d495541a2f9461221db6548e9d33dd0214`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0fbd74aa43a76fda511f0ce74a94a5d495541a2f9461221db6548e9d33dd0214`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
