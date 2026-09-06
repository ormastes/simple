# Audit Specification

> Tests covering Security Audit, Dependency Audit, Code Quality Audit, Audit Report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audit Specification

## Scenarios

### Security Audit

#### check for unsafe blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- check for unsafe blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check for unsafe blocks")
val unsafe_count = 0
check(unsafe_count >= 0)
```

</details>

#### check for extern functions

- check for extern functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check for extern functions")
val extern_count = 5
check(extern_count >= 0)
```

</details>

#### check for hardcoded credentials

- check for hardcoded credentials


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check for hardcoded credentials")
val found = false
check(not found)
```

</details>

#### check for SQL injection

- check for SQL injection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check for SQL injection")
val vulnerable = false
check(not vulnerable)
```

</details>

#### check for command injection

- check for command injection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check for command injection")
val vulnerable = false
check(not vulnerable)
```

</details>

### Dependency Audit

#### check outdated dependencies

- check outdated dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check outdated dependencies")
val outdated = 0
check(outdated >= 0)
```

</details>

#### check known vulnerabilities

- check known vulnerabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check known vulnerabilities")
val vulns = 0
check(vulns == 0)
```

</details>

#### check license compatibility

- check license compatibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check license compatibility")
val compatible = true
check(compatible)
```

</details>

#### check unused dependencies

- check unused dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check unused dependencies")
val unused = 0
check(unused >= 0)
```

</details>

### Code Quality Audit

#### check dead code

- check dead code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check dead code")
val dead_code_count = 0
check(dead_code_count >= 0)
```

</details>

#### check unused imports

- check unused imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check unused imports")
val unused = 0
check(unused >= 0)
```

</details>

#### check complexity

- check complexity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check complexity")
val max_complexity = 20
check(max_complexity > 0)
```

</details>

#### check line length

- check line length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check line length")
val max_line = 120
check(max_line > 0)
```

</details>

#### check function length

- check function length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check function length")
val max_fn = 100
check(max_fn > 0)
```

</details>

### Audit Report

#### report has severity levels

- report has severity levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report has severity levels")
val levels = ["critical", "high", "medium", "low", "info"]
check(levels.len() == 5)
```

</details>

#### report has finding count

- report has finding count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report has finding count")
val count = 0
check(count >= 0)
```

</details>

#### report has file locations

- report has file locations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report has file locations")
val has_locations = true
check(has_locations)
```

</details>

#### report has recommendations

- report has recommendations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report has recommendations")
val has_recs = true
check(has_recs)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/audit/audit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Security Audit, Dependency Audit, Code Quality Audit, Audit Report.
- Security Audit
- Dependency Audit
- Code Quality Audit
- Audit Report

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb67893c6fd2830f210d47b1656991b7dbcad3743a9ab993fea6ad57c5e930b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb67893c6fd2830f210d47b1656991b7dbcad3743a9ab993fea6ad57c5e930b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb67893c6fd2830f210d47b1656991b7dbcad3743a9ab993fea6ad57c5e930b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/audit/audit_spec.spl
mirror: doc/06_spec/unit/app/audit/audit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/audit/audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/audit/audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/audit/audit_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check for unsafe blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/audit/audit_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check for extern functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/audit/audit_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check for hardcoded credentials' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
