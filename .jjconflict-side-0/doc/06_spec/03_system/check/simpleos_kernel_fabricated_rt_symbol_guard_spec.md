# Simpleos Kernel Fabricated Rt Symbol Guard Specification

> Tests covering SimpleOS guest kernel fabricated rt_* symbol guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Kernel Fabricated Rt Symbol Guard Specification

## Scenarios

### SimpleOS guest kernel fabricated rt_* symbol guard

#### proves it actually inspected the kernel image

- proves it actually inspected the kernel image
   - Expected: nm_result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proves it actually inspected the kernel image")
# Without this the two assertions below could pass on an empty
# symbol table -- the same do-nothing pass this spec exists to
# forbid.
print "    audited image: {elf}"
print "    rt_* bodies disassembled: {inspected}, fabricated: {fabricated_total}"
expect(nm_result.2).to_equal(0)
expect(inspected).to_be_greater_than(0)
expect(fabricated_total).to_be_greater_than(0)
```

</details>

#### rejects any fabricated rt_* symbol outside the allowlist

- rejects any fabricated rt_* symbol outside the allowlist
   - Expected: new_fabricated.join(" ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects any fabricated rt_* symbol outside the allowlist")
# Subset assertion, never a count: a NEW fabrication fails here
# while a fixed one can be deleted from the allowlist alone.
expect(new_fabricated.join(" ")).to_equal("")
```

</details>

#### keeps weak-bound rt_* symbols confined to deliberate override points

- keeps weak-bound rt_* symbols confined to deliberate override points
   - Expected: new_weak.join(" ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps weak-bound rt_* symbols confined to deliberate override points")
expect(new_weak.join(" ")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS guest kernel fabricated rt_* symbol guard.
- SimpleOS guest kernel fabricated rt_* symbol guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `6dd98a10936b992cf0d05805b2e6899ecc1bfa29e3d8603202bac79fe7f1759e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dd98a10936b992cf0d05805b2e6899ecc1bfa29e3d8603202bac79fe7f1759e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dd98a10936b992cf0d05805b2e6899ecc1bfa29e3d8603202bac79fe7f1759e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl
mirror: doc/06_spec/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl:586:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves it actually inspected the kernel image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl:598:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects any fabricated rt_* symbol outside the allowlist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl:605:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps weak-bound rt_* symbols confined to deliberate override points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
