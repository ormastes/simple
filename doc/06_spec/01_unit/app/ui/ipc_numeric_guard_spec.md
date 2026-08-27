# Ipc Numeric Guard Specification

> Tests covering ipc numeric guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Numeric Guard Specification

## Scenarios

### ipc numeric guards

#### guards integer parsing at IPC boundaries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards integer parsing at IPC boundaries
   - Expected: ipc_int_or("600", -1) equals `600`
   - Expected: ipc_int_or(" 80 ", -1) equals `80`
   - Expected: ipc_int_or("", -1) equals `-1`
   - Expected: ipc_int_or("60x0", -1) equals `-1`
   - Expected: ipc_int_or("--5", -1) equals `-1`
   - Expected: ipc_int_or("ok", 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards integer parsing at IPC boundaries")
# oracle: digit-only fields parse exactly; malformed fields fall back to the declared default
expect(ipc_int_or("600", -1)).to_equal(600)
expect(ipc_int_or(" 80 ", -1)).to_equal(80)
expect(ipc_int_or("", -1)).to_equal(-1)
expect(ipc_int_or("60x0", -1)).to_equal(-1)
expect(ipc_int_or("--5", -1)).to_equal(-1)
expect(ipc_int_or("ok", 0)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ipc_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ipc numeric guards.
- ipc numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61eea9b125babe5a8f37a963c54f4b9ef5e80827c0446c1ac056a2443439fe9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61eea9b125babe5a8f37a963c54f4b9ef5e80827c0446c1ac056a2443439fe9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61eea9b125babe5a8f37a963c54f4b9ef5e80827c0446c1ac056a2443439fe9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/ui/ipc_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/ui/ipc_numeric_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/ipc_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/ipc_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/ipc_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/ipc_numeric_guard_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards integer parsing at IPC boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
