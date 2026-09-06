# 18 Window Open Capture Specification

> Tests covering T32 window open capture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 18 Window Open Capture Specification

## Scenarios

### T32 window open capture

#### register window capture

#### opens Register window

- opens Register window


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opens Register window")
val result = t32_hw_run_cmd(client, "Register /SpotLight")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Register /SpotLight failed: {e}").to_equal("")
```

</details>

#### captures Register text

- captures Register text
   - Expected: "Register /All failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("captures Register text")
val result = t32_hw_run_cmd(client, "Register /All")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("Register /All failed: {e}").to_equal("")
```

</details>

#### register read API

#### read_all_registers returns data

- read_all_registers returns data
   - Expected: "read_all_registers failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read_all_registers returns data")
val result = client.read_all_registers()
match result:
    Ok(regs):
        expect(regs.len()).to_be_greater_than(0)
    Err(e):
        expect("read_all_registers failed: {e}").to_equal("")
```

</details>

#### read PC register

- read PC register
   - Expected: "read_register PC failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("read PC register")
val result = client.read_register("PC")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("read_register PC failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/18_window_open_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 window open capture.
- T32 window open capture

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a32268b197e26e2faf1e3f1c92999cacee52315e5dc8c54b6c716415931cbe1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a32268b197e26e2faf1e3f1c92999cacee52315e5dc8c54b6c716415931cbe1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a32268b197e26e2faf1e3f1c92999cacee52315e5dc8c54b6c716415931cbe1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/18_window_open_capture_spec.spl
mirror: doc/06_spec/integration/t32_hw/18_window_open_capture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/18_window_open_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/18_window_open_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/18_window_open_capture_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens Register window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/18_window_open_capture_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures Register text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/18_window_open_capture_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_all_registers returns data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
