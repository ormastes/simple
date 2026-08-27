# Todo Scan Blocked Status Specification

> Tests covering todo_scan blocked status.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Todo Scan Blocked Status Specification

## Scenarios

### todo_scan blocked status

#### records a TODO carrying [blocked:reason] as status blocked

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records a TODO carrying [blocked:reason] as status blocked
   - Expected: entries.len() equals `1`
   - Expected: entries[0].blocked equals `no-self-hosted-deploy`
   - Expected: entries[0].status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("records a TODO carrying [blocked:reason] as status blocked")
dir_create_all("/tmp/todo_scan_spec")
val path = "/tmp/todo_scan_spec/blocked_fixture.spl"
file_write(path, "# TODO: [demo][P1] blocked demo item [blocked:no-self-hosted-deploy]\n")

val entries = scan_file(path, 0)
expect(entries.len()).to_equal(1)
expect(entries[0].blocked).to_equal("no-self-hosted-deploy")
expect(entries[0].status).to_equal("blocked")
```

</details>

#### leaves an unblocked TODO as status open

- leaves an unblocked TODO as status open
   - Expected: entries.len() equals `1`
   - Expected: entries[0].blocked equals ``
   - Expected: entries[0].status equals `open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("leaves an unblocked TODO as status open")
dir_create_all("/tmp/todo_scan_spec")
val path = "/tmp/todo_scan_spec/open_fixture.spl"
file_write(path, "# TODO: [demo][P2] plain actionable item\n")

val entries = scan_file(path, 0)
expect(entries.len()).to_equal(1)
expect(entries[0].blocked).to_equal("")
expect(entries[0].status).to_equal("open")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/todo_scan_blocked_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering todo_scan blocked status.
- todo_scan blocked status

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `2e4569ca55c9e9ee2b11c7a555b7a6db68c8cda3ef26fa8bc39949ad91ded14c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e4569ca55c9e9ee2b11c7a555b7a6db68c8cda3ef26fa8bc39949ad91ded14c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e4569ca55c9e9ee2b11c7a555b7a6db68c8cda3ef26fa8bc39949ad91ded14c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/todo_scan_blocked_status_spec.spl
mirror: doc/06_spec/01_unit/app/todo_scan_blocked_status_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/todo_scan_blocked_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/todo_scan_blocked_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/todo_scan_blocked_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/todo_scan_blocked_status_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a TODO carrying [blocked:reason] as status blocked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/todo_scan_blocked_status_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves an unblocked TODO as status open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
