# Cortex-M33 Target Preset Specification

> Verifies that `preset_cortex_m33()` returns the correct ARMv8-M Mainline target configuration and that it integrates with `preset_by_name()` and `preset_all_names()`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cortex-M33 Target Preset Specification

Verifies that `preset_cortex_m33()` returns the correct ARMv8-M Mainline target configuration and that it integrates with `preset_by_name()` and `preset_all_names()`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNOQ-PORT |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/compiler/backend/target_presets_m33_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `preset_cortex_m33()` returns the correct ARMv8-M Mainline
target configuration and that it integrates with `preset_by_name()` and
`preset_all_names()`.

## Behavior

- arch must be `thumbv8m.main` (ARMv8-M Mainline, not thumbv7em)
- ABI must be `eabihf` (STM32U585 has hardware FPU)
- Float support enabled
- Stack size 16384 (larger SRAM allows bigger stack than M4 default)
- Pointer width 32 (Cortex-M33 is 32-bit)
- Discoverable via `preset_by_name("cortex-m33")`
- Listed in `preset_all_names()`

## Scenarios

### preset_cortex_m33

#### AC-1: arch is thumbv8m.main

- AC-1: arch is thumbv8m.main
   - Expected: p.arch equals `thumbv8m.main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: arch is thumbv8m.main")
val p = preset_cortex_m33()
expect(p.arch).to_equal("thumbv8m.main")
```

</details>

#### AC-1: abi is eabihf

- AC-1: abi is eabihf
   - Expected: p.abi equals `eabihf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: abi is eabihf")
val p = preset_cortex_m33()
expect(p.abi).to_equal("eabihf")
```

</details>

#### AC-1: float_support is true

- AC-1: float_support is true
   - Expected: p.float_support is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: float_support is true")
val p = preset_cortex_m33()
expect(p.float_support).to_equal(true)
```

</details>

#### AC-1: stack_size is 16384

- AC-1: stack_size is 16384
   - Expected: p.stack_size equals `16384`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: stack_size is 16384")
val p = preset_cortex_m33()
expect(p.stack_size).to_equal(16384)
```

</details>

#### AC-1: pointer_width is 32

- AC-1: pointer_width is 32
   - Expected: p.pointer_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: pointer_width is 32")
val p = preset_cortex_m33()
expect(p.pointer_width).to_equal(32)
```

</details>

### preset_cortex_m33 discovery

#### AC-1: preset_by_name returns cortex-m33 with correct arch

- AC-1: preset_by_name returns cortex-m33 with correct arch
   - Expected: p.arch equals `thumbv8m.main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: preset_by_name returns cortex-m33 with correct arch")
val p = preset_by_name("cortex-m33")
expect(p.arch).to_equal("thumbv8m.main")
```

</details>

#### AC-1: preset_all_names contains cortex-m33

- AC-1: preset_all_names contains cortex-m33


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: preset_all_names contains cortex-m33")
val names = preset_all_names()
expect(names).to_contain("cortex-m33")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `fe88dc27d2a0fa17b701a1854c658e938c13a337fe96082ea340dbf5127df6b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe88dc27d2a0fa17b701a1854c658e938c13a337fe96082ea340dbf5127df6b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe88dc27d2a0fa17b701a1854c658e938c13a337fe96082ea340dbf5127df6b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/backend/target_presets_m33_spec.spl
mirror: doc/06_spec/unit/compiler/backend/target_presets_m33_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/target_presets_m33_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/target_presets_m33_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/target_presets_m33_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/target_presets_m33_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: arch is thumbv8m.main' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/target_presets_m33_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: abi is eabihf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/target_presets_m33_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: float_support is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
