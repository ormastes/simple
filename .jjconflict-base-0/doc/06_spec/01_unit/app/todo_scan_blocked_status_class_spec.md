# Todo Scan Blocked Status Class Specification

> Tests covering todo_scan marker parsing (positive control), todo_scan status derives from the blocked tag.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Todo Scan Blocked Status Class Specification

## Scenarios

### todo_scan marker parsing (positive control)

#### actually parses area, priority and description from a formatted marker

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actually parses area, priority and description from a formatted marker
   - Expected: parsed.area equals `render-perf`
   - Expected: parsed.priority equals `P1`
   - Expected: parsed.description equals `measure the 8K80 lane`
   - Expected: parsed.blocked equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("actually parses area, priority and description from a formatted marker")
val parsed = parse_todo_text("[render-perf][P1] measure the 8K80 lane")
expect(parsed.area).to_equal("render-perf")
expect(parsed.priority).to_equal("P1")
expect(parsed.description).to_equal("measure the 8K80 lane")
expect(parsed.blocked).to_equal("")
```

</details>

#### normalizes a priority alias, proving the parser is not returning defaults

- normalizes a priority alias, proving the parser is not returning defaults
   - Expected: parsed.priority equals `P1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normalizes a priority alias, proving the parser is not returning defaults")
val parsed = parse_todo_text("[demo][high] aliased priority")
expect(parsed.priority).to_equal("P1")
```

</details>

### todo_scan status derives from the blocked tag

#### separates the blocked reason from the description

- separates the blocked reason from the description
   - Expected: parsed.blocked equals `hardware-absent`
   - Expected: parsed.description equals `do the thing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("separates the blocked reason from the description")
val parsed = parse_todo_text("[demo][P1] do the thing [blocked:hardware-absent]")
expect(parsed.blocked).to_equal("hardware-absent")
expect(parsed.description).to_equal("do the thing")
```

</details>

#### keeps issue and blocked tags independent

- keeps issue and blocked tags independent
   - Expected: parsed.issue equals `42`
   - Expected: parsed.blocked equals `hardware-absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps issue and blocked tags independent")
val parsed = parse_todo_text("[demo][P1] do the thing [#42] [blocked:hardware-absent]")
expect(parsed.issue).to_equal("42")
expect(parsed.blocked).to_equal("hardware-absent")
```

</details>

#### keeps issue and blocked tags independent in either order

- keeps issue and blocked tags independent in either order
   - Expected: parsed.issue equals `42`
   - Expected: parsed.blocked equals `hardware-absent`
   - Expected: parsed.description equals `do the thing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps issue and blocked tags independent in either order")
val parsed = parse_todo_text("[demo][P1] do the thing [blocked:hardware-absent] [#42]")
expect(parsed.issue).to_equal("42")
expect(parsed.blocked).to_equal("hardware-absent")
expect(parsed.description).to_equal("do the thing")
```

</details>

#### classifies a mixed file so blocked and open rows stay distinguishable

- classifies a mixed file so blocked and open rows stay distinguishable
   - Expected: entries.len() equals `3`
   - Expected: entries[0].status equals `blocked`
   - Expected: entries[1].status equals `open`
   - Expected: entries[2].status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("classifies a mixed file so blocked and open rows stay distinguishable")
dir_create_all("/tmp/todo_scan_spec")
val path = "/tmp/todo_scan_spec/mixed_fixture.spl"
file_write(path, "# TODO: [demo][P1] blocked one [blocked:hardware-absent]\n# TODO: [demo][P1] open one\n# TODO: [demo][P2] blocked two [blocked:no-self-hosted-deploy]\n")

val entries = scan_file(path, 0)
expect(entries.len()).to_equal(3)
expect(entries[0].status).to_equal("blocked")
expect(entries[1].status).to_equal("open")
expect(entries[2].status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/todo_scan_blocked_status_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering todo_scan marker parsing (positive control), todo_scan status derives from the blocked tag.
- todo_scan marker parsing (positive control)
- todo_scan status derives from the blocked tag

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `61826005a31233a68f9369eff02d18b86ac197cb9f570e39eb47dd2f519c1e78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61826005a31233a68f9369eff02d18b86ac197cb9f570e39eb47dd2f519c1e78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61826005a31233a68f9369eff02d18b86ac197cb9f570e39eb47dd2f519c1e78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/todo_scan_blocked_status_class_spec.spl
mirror: doc/06_spec/01_unit/app/todo_scan_blocked_status_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/todo_scan_blocked_status_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/todo_scan_blocked_status_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/todo_scan_blocked_status_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/todo_scan_blocked_status_class_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually parses area, priority and description from a formatted marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/todo_scan_blocked_status_class_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes a priority alias, proving the parser is not returning defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/todo_scan_blocked_status_class_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separates the blocked reason from the description' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
