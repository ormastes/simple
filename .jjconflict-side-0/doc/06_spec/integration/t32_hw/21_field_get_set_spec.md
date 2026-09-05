# 21 Field Get Set Specification

> Tests covering T32 field get/set.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 21 Field Get Set Specification

## Scenarios

### T32 field get/set

#### register reads

#### reads PC register via eval

- reads PC register via eval
   - Expected: "eval PC failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads PC register via eval")
val result = t32_hw_eval(client, "Register(PC)")
match result:
    Ok(v):
        # PC should return a hex value string
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval PC failed: {e}").to_equal("")
```

</details>

#### reads SP register via eval

- reads SP register via eval
   - Expected: "eval SP failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads SP register via eval")
val result = t32_hw_eval(client, "Register(SP)")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval SP failed: {e}").to_equal("")
```

</details>

#### register writes

#### writes PC register

- writes PC register


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes PC register")
val result = t32_hw_run_cmd(client, "Register.Set PC 0x08000000")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Register.Set PC failed: {e}").to_equal("")
```

</details>

#### verifies PC was set

- verifies PC was set
   - Expected: "verify PC failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifies PC was set")
# Write a known value then read it back
t32_hw_run_cmd(client, "Register.Set PC 0x08000000")
val result = t32_hw_eval(client, "Register(PC)")
match result:
    Ok(v):
        expect(v).to_contain("08000000")
    Err(e):
        expect("verify PC failed: {e}").to_equal("")
```

</details>

#### system mode

#### reads system mode field

- reads system mode field
   - Expected: "SYStem.MODE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads system mode field")
val result = t32_hw_eval(client, "SYStem.MODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("SYStem.MODE() failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/21_field_get_set_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 field get/set.
- T32 field get/set

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67f49d7c02a97d1e56836919c04a8176c06e518b736535ca3cde05aa8a77b53e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67f49d7c02a97d1e56836919c04a8176c06e518b736535ca3cde05aa8a77b53e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67f49d7c02a97d1e56836919c04a8176c06e518b736535ca3cde05aa8a77b53e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/21_field_get_set_spec.spl
mirror: doc/06_spec/integration/t32_hw/21_field_get_set_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/21_field_get_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/21_field_get_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/21_field_get_set_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads PC register via eval' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/21_field_get_set_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads SP register via eval' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/21_field_get_set_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes PC register' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
