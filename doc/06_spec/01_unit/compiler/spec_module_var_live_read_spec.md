# Spec Module Var Live Read Specification

> Tests covering an it body reads module-level state live, not as a registration-time snapshot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Module Var Live Read Specification

## Scenarios

### an it body reads module-level state live, not as a registration-time snapshot

#### case A: helper-write then helper-read sees the new value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- case A: helper-write then helper-read sees the new value
- bump() writes both module vars
- A helper reading the same var is the control arm — it always worked, and proves the write landed in MODULE_GLOBALS
   - Expected: read_counter() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("case A: helper-write then helper-read sees the new value")
step("bump() writes both module vars")
bump()

step("A helper reading the same var is the control arm — it always worked, and proves the write landed in MODULE_GLOBALS")
expect(read_counter()).to_equal(1)
```

</details>

#### case B: helper-write then DIRECT read in the it body sees the new value

- case B: helper-write then DIRECT read in the it body sees the new value
- counter is 1 from case A; bump() makes it 2 and sets log_text
- This is the defect: the direct read returned the stale pre-helper value (0 / init)
   - Expected: counter equals `2`
   - Expected: log_text equals `written`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("case B: helper-write then DIRECT read in the it body sees the new value")
step("counter is 1 from case A; bump() makes it 2 and sets log_text")
bump()

step("This is the defect: the direct read returned the stale pre-helper value (0 / init)")
expect(counter).to_equal(2)
expect(log_text).to_equal("written")
```

</details>

#### case C: direct-write then direct-read in the same body

- case C: direct-write then direct-read in the same body
- A write performed inside the body must be visible to that same body
   - Expected: counter equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("case C: direct-write then direct-read in the same body")
step("A write performed inside the body must be visible to that same body")
counter = 17
expect(counter).to_equal(17)
```

</details>

#### case D: direct-write then helper-read

- case D: direct-write then helper-read
- A write performed inside the body must also reach the global store a helper reads
   - Expected: read_counter() equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("case D: direct-write then helper-read")
step("A write performed inside the body must also reach the global store a helper reads")
counter = 18
expect(read_counter()).to_equal(18)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/spec_module_var_live_read_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering an it body reads module-level state live, not as a registration-time snapshot.
- an it body reads module-level state live, not as a registration-time snapshot

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1b9d6f213d52ca393fc0c52469bd7e68be7b7fe3450d054e71ffe25b79bd17f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1b9d6f213d52ca393fc0c52469bd7e68be7b7fe3450d054e71ffe25b79bd17f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1b9d6f213d52ca393fc0c52469bd7e68be7b7fe3450d054e71ffe25b79bd17f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/spec_module_var_live_read_spec.spl
mirror: doc/06_spec/01_unit/compiler/spec_module_var_live_read_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/spec_module_var_live_read_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/spec_module_var_live_read_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/spec_module_var_live_read_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/spec_module_var_live_read_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case A: helper-write then helper-read sees the new value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/spec_module_var_live_read_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case B: helper-write then DIRECT read in the it body sees the new value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/spec_module_var_live_read_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case C: direct-write then direct-read in the same body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
