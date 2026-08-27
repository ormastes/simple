# Platform Spec Verification Specification

> Tests covering Enum Variant with Data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Spec Verification Specification

## Scenarios

### Enum Variant with Data

#### creates composite mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates composite mode
   - Expected: has_parens is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates composite mode")
val mode_str = "interpreter(remote(baremetal(riscv32)))"
val has_parens = mode_str.contains("(")
expect(has_parens).to_equal(true)
```

</details>

#### creates simple interpreter mode

- creates simple interpreter mode
   - Expected: has_parens is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates simple interpreter mode")
val mode_str = "interpreter"
val has_parens = mode_str.contains("(")
expect(has_parens).to_equal(false)
```

</details>

#### extracts runtime from composite

- extracts runtime from composite
   - Expected: runtime equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts runtime from composite")
val spec = "interpreter(remote(baremetal(riscv32)))"
val first_paren = spec.index_of("(")
val runtime = spec[0:first_paren]
expect(runtime).to_equal("interpreter")
```

</details>

#### detects layers

- detects layers
   - Expected: has_remote is true
   - Expected: has_baremetal is true
   - Expected: has_riscv is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects layers")
val spec = "interpreter(remote(baremetal(riscv32)))"
val has_remote = spec.contains("remote")
val has_baremetal = spec.contains("baremetal")
val has_riscv = spec.contains("riscv32")
expect(has_remote).to_equal(true)
expect(has_baremetal).to_equal(true)
expect(has_riscv).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/manual/platform_spec_verification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Enum Variant with Data.
- Enum Variant with Data

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81ee08053df14dc94e93a7a4c968faf4251d8fe3fcca381ee680837762d0e9aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81ee08053df14dc94e93a7a4c968faf4251d8fe3fcca381ee680837762d0e9aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81ee08053df14dc94e93a7a4c968faf4251d8fe3fcca381ee680837762d0e9aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/manual/platform_spec_verification_spec.spl
mirror: doc/06_spec/03_system/tools/manual/platform_spec_verification_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/manual/platform_spec_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/manual/platform_spec_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/manual/platform_spec_verification_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates composite mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/manual/platform_spec_verification_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates simple interpreter mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/manual/platform_spec_verification_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts runtime from composite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
