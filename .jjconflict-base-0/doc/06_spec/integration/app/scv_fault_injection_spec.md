# scv_fault_injection_spec

> Purpose: This spec proves the SCV snapshot path follows the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_fault_injection_spec

Purpose: This spec proves the SCV snapshot path follows the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_fault_injection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV snapshot path follows the
write-new-then-publish protocol (stabilization report §6): a crash injected
after any write step leaves the repository in the OLD or NEW state, never half.
Faults are injected via `SCV_FAULT_AFTER=<content|tree|commit|operation|head>`.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### scv snapshot fault injection

#### stays on the old state when crashed after content writes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stays on the old state when crashed after content writes
- Inject a crash after content object writes, restart, verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stays on the old state when crashed after content writes")
step("Inject a crash after content object writes, restart, verify")
val out = _run(_fault_script("content"))
_expect_old_or_new(out, "content", "old")
```

</details>

#### stays on the old state when crashed after the tree write

- stays on the old state when crashed after the tree write
- Inject a crash after the tree write, restart, verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stays on the old state when crashed after the tree write")
step("Inject a crash after the tree write, restart, verify")
val out = _run(_fault_script("tree"))
_expect_old_or_new(out, "tree", "old")
```

</details>

#### stays on the old state when crashed after the commit write

- stays on the old state when crashed after the commit write
- Inject a crash after the commit write, restart, verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stays on the old state when crashed after the commit write")
step("Inject a crash after the commit write, restart, verify")
val out = _run(_fault_script("commit"))
_expect_old_or_new(out, "commit", "old")
```

</details>

#### stays on the old state when crashed after the operation write

- stays on the old state when crashed after the operation write
- Inject a crash after the operation object write, restart, verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stays on the old state when crashed after the operation write")
step("Inject a crash after the operation object write, restart, verify")
val out = _run(_fault_script("operation"))
_expect_old_or_new(out, "operation", "old")
```

</details>

#### lands on the new state when crashed after head publication

- lands on the new state when crashed after head publication
- Inject a crash after the head marker write, restart, verify
- Doctor reconciles the derived workspace pointer to the new head


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lands on the new state when crashed after head publication")
step("Inject a crash after the head marker write, restart, verify")
val out = _run(_fault_script("head"))
step("Doctor reconciles the derived workspace pointer to the new head")
_expect_old_or_new(out, "head", "new")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-FAULT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cbb8a28271c7c8dc283d1f3536e06e9232818b1ac75778caf5f6736be394be68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cbb8a28271c7c8dc283d1f3536e06e9232818b1ac75778caf5f6736be394be68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cbb8a28271c7c8dc283d1f3536e06e9232818b1ac75778caf5f6736be394be68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_fault_injection_spec.spl
mirror: doc/06_spec/integration/app/scv_fault_injection_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_fault_injection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_fault_injection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_fault_injection_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_fault_injection_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays on the old state when crashed after content writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_fault_injection_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays on the old state when crashed after the tree write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_fault_injection_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays on the old state when crashed after the commit write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
