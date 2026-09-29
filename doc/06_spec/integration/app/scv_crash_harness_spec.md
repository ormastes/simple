# scv_crash_harness_spec

> Purpose: Proves the SCV crash/fault-injection harness (SCV-MIG-18,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_crash_harness_spec

Purpose: Proves the SCV crash/fault-injection harness (SCV-MIG-18,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_crash_harness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Proves the SCV crash/fault-injection harness (SCV-MIG-18,
scripts/check/check-scv-crash-harness.shs) works end to end: its selftest
catches a deliberately-corrupted repository as FAIL, and a live run over a
real fault point plus the head-delete chaos row survives with the house PASS
verdict as the last stdout line. The full 6-point sweep is the step script
SCV-MIG-18.shs; this spec runs a budgeted subset so it fits the test timeout.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### SCV crash harness

#### selftest catches a deliberately corrupted repository as FAIL

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selftest catches a deliberately corrupted repository as FAIL
   - Expected: code equals `0`
   - Expected: err does not contain `SELFTEST FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("selftest catches a deliberately corrupted repository as FAIL")
val (out, err, code) = rt_process_run("/bin/sh", ["scripts/check/check-scv-crash-harness.shs", "--selftest"])
expect(code).to_equal(0)
expect(_last_line(out)).to_contain("PASS — selftest only")
expect(err.contains("SELFTEST FAIL")).to_equal(false)
```

</details>

#### survives the content fault point and the head-delete chaos row

- survives the content fault point and the head-delete chaos row
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("survives the content fault point and the head-delete chaos row")
val (out, _err, code) = rt_process_run("/bin/sh", ["scripts/check/check-scv-crash-harness.shs", "--points", "content", "--chaos", "head-delete"])
expect(_last_line(out)).to_contain("PASS — 2 crash point(s) survived, 0 corruptions")
expect(code).to_equal(0)
```

</details>

#### reports ERROR, never a pass, when nothing was checked

- reports ERROR, never a pass, when nothing was checked
   - Expected: code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports ERROR, never a pass, when nothing was checked")
val (out, _err, code) = rt_process_run("/bin/sh", ["scripts/check/check-scv-crash-harness.shs", "--bogus-flag"])
expect(code).to_equal(2)
expect(_last_line(out)).to_contain("ERROR — nothing was checked")
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-CRASH-HARNESS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8b5bc57f7f6ecc43d45721652d0d18802147c04efe1e3ea1f7e12093dce4185`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8b5bc57f7f6ecc43d45721652d0d18802147c04efe1e3ea1f7e12093dce4185`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8b5bc57f7f6ecc43d45721652d0d18802147c04efe1e3ea1f7e12093dce4185`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_crash_harness_spec.spl
mirror: doc/06_spec/integration/app/scv_crash_harness_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_crash_harness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_crash_harness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_crash_harness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_crash_harness_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_crash_harness_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selftest catches a deliberately corrupted repository as FAIL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_crash_harness_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'survives the content fault point and the head-delete chaos row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_crash_harness_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports ERROR, never a pass, when nothing was checked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
