# Hal Trait Surface Specification

> Tests covering AC-3 — 16 HAL traits declared in arch/hal.spl, AC-3 — per-arch impls present for 14 implementable traits, AC-3 — arch-neutral kernel uses only os.kernel.arch.hal, AC-3 — per-arch LoC delta ≥40% (or ≥25% with rationale).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Trait Surface Specification

## Scenarios

### AC-3 — 16 HAL traits declared in arch/hal.spl

#### hal.spl exists

- hal.spl exists
   - Expected: file_exists(HAL_PATH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hal.spl exists")
expect(file_exists(HAL_PATH)).to_equal(true)
```

</details>

#### declares HalConsole (existing)

- declares HalConsole (existing)
   - Expected: body contains `trait HalConsole`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalConsole (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalConsole")).to_equal(true)
```

</details>

#### declares HalBoot (existing)

- declares HalBoot (existing)
   - Expected: body contains `trait HalBoot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalBoot (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalBoot")).to_equal(true)
```

</details>

#### declares HalCpu (existing)

- declares HalCpu (existing)
   - Expected: body contains `trait HalCpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalCpu (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCpu")).to_equal(true)
```

</details>

#### declares HalPower (existing)

- declares HalPower (existing)
   - Expected: body contains `trait HalPower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalPower (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalPower")).to_equal(true)
```

</details>

#### declares HalPaging (existing)

- declares HalPaging (existing)
   - Expected: body contains `trait HalPaging`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalPaging (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalPaging")).to_equal(true)
```

</details>

#### declares HalInterrupt (existing)

- declares HalInterrupt (existing)
   - Expected: body contains `trait HalInterrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalInterrupt (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalInterrupt")).to_equal(true)
```

</details>

#### declares HalTimer (existing)

- declares HalTimer (existing)
   - Expected: body contains `trait HalTimer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalTimer (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalTimer")).to_equal(true)
```

</details>

#### declares HalContext (existing)

- declares HalContext (existing)
   - Expected: body contains `trait HalContext`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalContext (existing)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalContext")).to_equal(true)
```

</details>

#### declares HalEntropy (NEW — R6 canary entropy)

- declares HalEntropy (NEW — R6 canary entropy)
   - Expected: body contains `trait HalEntropy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalEntropy (NEW — R6 canary entropy)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalEntropy")).to_equal(true)
```

</details>

#### declares HalCstart (NEW — replaces simpleos_crt0.S/setjmp.S)

- declares HalCstart (NEW — replaces simpleos_crt0.S/setjmp.S)
   - Expected: body contains `trait HalCstart`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalCstart (NEW — replaces simpleos_crt0.S/setjmp.S)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCstart")).to_equal(true)
```

</details>

#### declares HalSyscall (NEW — capability-checked trampoline)

- declares HalSyscall (NEW — capability-checked trampoline)
   - Expected: body contains `trait HalSyscall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalSyscall (NEW — capability-checked trampoline)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalSyscall")).to_equal(true)
```

</details>

#### declares HalCanary (NEW — per-boot stack guard)

- declares HalCanary (NEW — per-boot stack guard)
   - Expected: body contains `trait HalCanary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalCanary (NEW — per-boot stack guard)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCanary")).to_equal(true)
```

</details>

#### declares HalBarrier (NEW — MMIO ordering)

- declares HalBarrier (NEW — MMIO ordering)
   - Expected: body contains `trait HalBarrier`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalBarrier (NEW — MMIO ordering)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalBarrier")).to_equal(true)
```

</details>

#### declares HalCache (NEW — i/d-cache maintenance)

- declares HalCache (NEW — i/d-cache maintenance)
   - Expected: body contains `trait HalCache`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalCache (NEW — i/d-cache maintenance)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCache")).to_equal(true)
```

</details>

#### declares HalSmp (NEW — RESERVED, shape only)

- declares HalSmp (NEW — RESERVED, shape only)
   - Expected: body contains `trait HalSmp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalSmp (NEW — RESERVED, shape only)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalSmp")).to_equal(true)
```

</details>

#### declares HalPerCpu (NEW — RESERVED, shape only)

- declares HalPerCpu (NEW — RESERVED, shape only)
   - Expected: body contains `trait HalPerCpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares HalPerCpu (NEW — RESERVED, shape only)")
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalPerCpu")).to_equal(true)
```

</details>

### AC-3 — per-arch impls present for 14 implementable traits

#### x86_64 cstart.spl exists

- x86_64 cstart.spl exists
   - Expected: file_exists("src/os/kernel/arch/x86_64/cstart.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 cstart.spl exists")
expect(file_exists("src/os/kernel/arch/x86_64/cstart.spl")).to_equal(true)
```

</details>

#### x86_32 cstart.spl exists

- x86_32 cstart.spl exists
   - Expected: file_exists("src/os/kernel/arch/x86_32/cstart.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_32 cstart.spl exists")
expect(file_exists("src/os/kernel/arch/x86_32/cstart.spl")).to_equal(true)
```

</details>

#### arm32 cstart.spl exists

- arm32 cstart.spl exists
   - Expected: file_exists("src/os/kernel/arch/arm32/cstart.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32 cstart.spl exists")
expect(file_exists("src/os/kernel/arch/arm32/cstart.spl")).to_equal(true)
```

</details>

#### arm64 cstart.spl exists

- arm64 cstart.spl exists
   - Expected: file_exists("src/os/kernel/arch/arm64/cstart.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64 cstart.spl exists")
expect(file_exists("src/os/kernel/arch/arm64/cstart.spl")).to_equal(true)
```

</details>

#### riscv32 cstart.spl exists

- riscv32 cstart.spl exists
   - Expected: file_exists("src/os/kernel/arch/riscv32/cstart.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32 cstart.spl exists")
expect(file_exists("src/os/kernel/arch/riscv32/cstart.spl")).to_equal(true)
```

</details>

#### riscv64 cstart.spl exists

- riscv64 cstart.spl exists
   - Expected: file_exists("src/os/kernel/arch/riscv64/cstart.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64 cstart.spl exists")
expect(file_exists("src/os/kernel/arch/riscv64/cstart.spl")).to_equal(true)
```

</details>

#### x86_64 entropy.spl exists

- x86_64 entropy.spl exists
   - Expected: file_exists("src/os/kernel/arch/x86_64/entropy.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 entropy.spl exists")
expect(file_exists("src/os/kernel/arch/x86_64/entropy.spl")).to_equal(true)
```

</details>

#### arm64 entropy.spl exists

- arm64 entropy.spl exists
   - Expected: file_exists("src/os/kernel/arch/arm64/entropy.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64 entropy.spl exists")
expect(file_exists("src/os/kernel/arch/arm64/entropy.spl")).to_equal(true)
```

</details>

#### riscv64 entropy.spl exists

- riscv64 entropy.spl exists
   - Expected: file_exists("src/os/kernel/arch/riscv64/entropy.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64 entropy.spl exists")
expect(file_exists("src/os/kernel/arch/riscv64/entropy.spl")).to_equal(true)
```

</details>

### AC-3 — arch-neutral kernel uses only os.kernel.arch.hal

#### loc report exists

- loc report exists
   - Expected: file_exists(LOC_REPORT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loc report exists")
expect(file_exists(LOC_REPORT)).to_equal(true)
```

</details>

#### loc report is a real measurement, not a static literal

- loc report is a real measurement, not a static literal
   - Expected: report contains `"arch_import_files_scanned":`
   - Expected: report contains `"direct_arch_import_samples":`
   - Expected: report does not contain `"arch_import_files_scanned": 0,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loc report is a real measurement, not a static literal")
"""Positive control. The absence assertion below is vacuous against a
missing or stale report, so first prove the generator actually scanned:
`arch_import_files_scanned` must be present and non-trivial, and the
samples field must exist. If the generator ever regresses back to
printing a hardcoded count, these two hits disappear and this fails."""
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"arch_import_files_scanned\":")).to_equal(true)
expect(report.contains("\"direct_arch_import_samples\":")).to_equal(true)
expect(report.contains("\"arch_import_files_scanned\": 0,")).to_equal(false)
```

</details>

#### report shows zero arch-specific imports outside arch/

- report shows zero arch-specific imports outside arch/
   - Expected: report contains `"direct_arch_imports_outside_arch": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report shows zero arch-specific imports outside arch/")
"""AC-3 contract: zero direct arch imports outside arch/ and
arch_adapt/. Measured 2026-08-11: 7 — this is RED on real drift, see
doc/08_tracking/bug/direct_arch_imports_outside_arch_2026-08-11.md.
Do NOT relax this number to obtain green; remove the imports."""
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"direct_arch_imports_outside_arch\": 0")).to_equal(true)
```

</details>

### AC-3 — per-arch LoC delta ≥40% (or ≥25% with rationale)

#### loc report contains per-arch delta_pct field

- loc report contains per-arch delta_pct field
   - Expected: report contains `"x86_64"`
   - Expected: report contains `"delta_pct"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loc report contains per-arch delta_pct field")
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"x86_64\"")).to_equal(true)
expect(report.contains("\"delta_pct\"")).to_equal(true)
```

</details>

#### x86_64 delta_pct meets the floor

- x86_64 delta_pct meets the floor
   - Expected: report contains `"x86_64_meets_floor": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 delta_pct meets the floor")
"""Read the report and assert x86_64 hit ≥40 (preferred) or
≥25 with documented walker fallback."""
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"x86_64_meets_floor\": true")).to_equal(true)
```

</details>

#### all six archs meet the floor

- all six archs meet the floor
   - Expected: report contains `"all_archs_meet_floor": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all six archs meet the floor")
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"all_archs_meet_floor\": true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/multiarch/hal_trait_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-3 — 16 HAL traits declared in arch/hal.spl, AC-3 — per-arch impls present for 14 implementable traits, AC-3 — arch-neutral kernel uses only os.kernel.arch.hal, AC-3 — per-arch LoC delta ≥40% (or ≥25% with rationale).
- AC-3 — 16 HAL traits declared in arch/hal.spl
- AC-3 — per-arch impls present for 14 implementable traits
- AC-3 — arch-neutral kernel uses only os.kernel.arch.hal
- AC-3 — per-arch LoC delta ≥40% (or ≥25% with rationale)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `fcfe211e19c0c91efd36a762bbddbe6a4a1547ccbeb4a1ef5055daacb7d5e2bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcfe211e19c0c91efd36a762bbddbe6a4a1547ccbeb4a1ef5055daacb7d5e2bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcfe211e19c0c91efd36a762bbddbe6a4a1547ccbeb4a1ef5055daacb7d5e2bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/multiarch/hal_trait_surface_spec.spl
mirror: doc/06_spec/unit/os/multiarch/hal_trait_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/multiarch/hal_trait_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/multiarch/hal_trait_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/multiarch/hal_trait_surface_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hal.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/hal_trait_surface_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares HalConsole (existing)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/hal_trait_surface_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares HalBoot (existing)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
