# Connection Matrix Qemu Specification

> Tests covering QEMU connection specs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Connection Matrix Qemu Specification

## Scenarios

### QEMU connection specs

<details>
<summary>Advanced: has 2 QEMU specs</summary>

#### has 2 QEMU specs _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has 2 QEMU specs
   - Expected: specs.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has 2 QEMU specs")
val specs = qemu_specs()
expect(specs.len()).to_equal(2)
```

</details>


</details>

<details>
<summary>Advanced: QEMU ARM uses port 3335</summary>

#### QEMU ARM uses port 3335 _(slow)_

- QEMU ARM uses port 3335
   - Expected: specs[0].gdb_port equals `3335`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("QEMU ARM uses port 3335")
val specs = qemu_specs()
expect(specs[0].gdb_port).to_equal(3335)
```

</details>


</details>

<details>
<summary>Advanced: QEMU RV32 uses port 1234</summary>

#### QEMU RV32 uses port 1234 _(slow)_

- QEMU RV32 uses port 1234
   - Expected: specs[1].gdb_port equals `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("QEMU RV32 uses port 1234")
val specs = qemu_specs()
expect(specs[1].gdb_port).to_equal(1234)
```

</details>


</details>

<details>
<summary>Advanced: QEMU specs are not hardware</summary>

#### QEMU specs are not hardware _(slow)_

- QEMU specs are not hardware
   - Expected: specs[0].is_hardware() is false
   - Expected: specs[1].is_hardware() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("QEMU specs are not hardware")
val specs = qemu_specs()
expect(specs[0].is_hardware()).to_equal(false)
expect(specs[1].is_hardware()).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/integration/baremetal/connection_matrix_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QEMU connection specs.
- QEMU connection specs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `4d3e71dbd2945d2b8ac52fe255fea63000f7dc0a287f0c0978133a98d75cde42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d3e71dbd2945d2b8ac52fe255fea63000f7dc0a287f0c0978133a98d75cde42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d3e71dbd2945d2b8ac52fe255fea63000f7dc0a287f0c0978133a98d75cde42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/baremetal/connection_matrix_qemu_spec.spl
mirror: doc/06_spec/integration/baremetal/connection_matrix_qemu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/baremetal/connection_matrix_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/baremetal/connection_matrix_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/baremetal/connection_matrix_qemu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/baremetal/connection_matrix_qemu_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has 2 QEMU specs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/baremetal/connection_matrix_qemu_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'QEMU ARM uses port 3335' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/baremetal/connection_matrix_qemu_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'QEMU RV32 uses port 1234' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
