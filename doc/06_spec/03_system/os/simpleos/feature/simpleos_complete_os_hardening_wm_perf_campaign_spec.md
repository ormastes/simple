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
| Updated | 2026-08-26 |
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

#### should accept complete live evidence for production SimpleOS window manager

- should accept complete live evidence for production SimpleOS window manager
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for production SimpleOS window manager")
step_exercise_window_manager()
check_simpleos_wm("REQ-017", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for production SimpleOS window manager</summary>

#### should preserve the selected boundary for production SimpleOS window manager

- should preserve the selected boundary for production SimpleOS window manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for production SimpleOS window manager")
step_exercise_window_manager()
check_simpleos_wm("REQ-017", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for production SimpleOS window manager</summary>

#### should reject missing stale substituted or invalid evidence for production SimpleOS window manager

- should reject missing stale substituted or invalid evidence for production SimpleOS window manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for production SimpleOS window manager")
step_exercise_window_manager()
check_simpleos_wm("REQ-017", "rejection")
```

</details>


</details>

### REQ-018: observability and performance ownership

#### should accept complete live evidence for observability and performance ownership

- should accept complete live evidence for observability and performance ownership
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for observability and performance ownership")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-018", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for observability and performance ownership</summary>

#### should preserve the selected boundary for observability and performance ownership

- should preserve the selected boundary for observability and performance ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for observability and performance ownership")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-018", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for observability and performance ownership</summary>

#### should reject missing stale substituted or invalid evidence for observability and performance ownership

- should reject missing stale substituted or invalid evidence for observability and performance ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for observability and performance ownership")
step_measure_resource_budget()
check_simpleos_perf_duplication("REQ-018", "rejection")
```

</details>


</details>

### NFR-002: strict performance budgets

#### should accept complete live evidence for strict performance budgets

- should accept complete live evidence for strict performance budgets
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for strict performance budgets")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-002", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for strict performance budgets</summary>

#### should preserve the selected boundary for strict performance budgets

- should preserve the selected boundary for strict performance budgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for strict performance budgets")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-002", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for strict performance budgets</summary>

#### should reject missing stale substituted or invalid evidence for strict performance budgets

- should reject missing stale substituted or invalid evidence for strict performance budgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for strict performance budgets")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-002", "rejection")
```

</details>


</details>

### NFR-003: reproducible measurement

#### should accept complete live evidence for reproducible measurement

- should accept complete live evidence for reproducible measurement
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for reproducible measurement")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-003", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for reproducible measurement</summary>

#### should preserve the selected boundary for reproducible measurement

- should preserve the selected boundary for reproducible measurement


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for reproducible measurement")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-003", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for reproducible measurement</summary>

#### should reject missing stale substituted or invalid evidence for reproducible measurement

- should reject missing stale substituted or invalid evidence for reproducible measurement


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for reproducible measurement")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-003", "rejection")
```

</details>


</details>

### NFR-004: mission-critical robustness

#### should accept complete live evidence for mission-critical robustness

- should accept complete live evidence for mission-critical robustness
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for mission-critical robustness")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-004", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for mission-critical robustness</summary>

#### should preserve the selected boundary for mission-critical robustness

- should preserve the selected boundary for mission-critical robustness


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for mission-critical robustness")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-004", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for mission-critical robustness</summary>

#### should reject missing stale substituted or invalid evidence for mission-critical robustness

- should reject missing stale substituted or invalid evidence for mission-critical robustness


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for mission-critical robustness")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-004", "rejection")
```

</details>


</details>

### NFR-005: static core and dynamic application bounds

#### should accept complete live evidence for static core and dynamic application bounds

- should accept complete live evidence for static core and dynamic application bounds
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for static core and dynamic application bounds")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-005", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for static core and dynamic application bounds</summary>

#### should preserve the selected boundary for static core and dynamic application bounds

- should preserve the selected boundary for static core and dynamic application bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for static core and dynamic application bounds")
step_measure_resource_budget()
check_simpleos_perf_duplication("NFR-005", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for static core and dynamic application bounds</summary>

#### should reject missing stale substituted or invalid evidence for static core and dynamic application bounds

- should reject missing stale substituted or invalid evidence for static core and dynamic application bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for static core and dynamic application bounds")
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

- Canonical SPipe generation for source `8dbd514a2cee2b348ff4a3d69e033c76005f9e3bce6f2b7cb877856c56949aa3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8dbd514a2cee2b348ff4a3d69e033c76005f9e3bce6f2b7cb877856c56949aa3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8dbd514a2cee2b348ff4a3d69e033c76005f9e3bce6f2b7cb877856c56949aa3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for production SimpleOS window manager' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept complete live evidence for production SimpleOS window manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:42:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for production SimpleOS window manager' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the selected boundary for production SimpleOS window manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for production SimpleOS window manager' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing stale substituted or invalid evidence for production SimpleOS window manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for observability and performance ownership' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for observability and performance ownership' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for observability and performance ownership' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
