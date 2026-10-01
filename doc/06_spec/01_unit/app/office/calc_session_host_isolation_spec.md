# Calc Session Host Isolation Specification

> Tests covering Calc session host production isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Calc Session Host Isolation Specification

## Scenarios

### Calc session host production isolation

#### keeps the normal terminal owner free of access and capture transports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the normal terminal owner free of access and capture transports


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the normal terminal owner free of access and capture transports")
val source = read_file("src/app/office/sheets/calc_session_host.spl").lower()
expect(source.contains("app.ui.standalone")).to_be(false)
expect(source.contains("test_api")).to_be(false)
expect(source.contains("tcp")).to_be(false)
expect(source.contains("sgtti")).to_be(false)
expect(source.contains("capture")).to_be(false)
```

</details>

<details>
<summary>Advanced: confines loopback transport to the explicit access adapter</summary>

#### confines loopback transport to the explicit access adapter

- confines loopback transport to the explicit access adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("confines loopback transport to the explicit access adapter")
val source = read_file("src/app/office/sheets/calc_access_session_host.spl")
expect(source).to_contain("app.ui.standalone.bootstrap")
expect(source).to_contain("TcpListener")
expect(source).to_contain("CalcSessionHost")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/calc_session_host_isolation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Calc session host production isolation.
- Calc session host production isolation

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

- Canonical SPipe generation for source `895d0c66e2923f510a501dc2a8f036601ecb01372c67df41ac6d4dc917e0379b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `895d0c66e2923f510a501dc2a8f036601ecb01372c67df41ac6d4dc917e0379b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `895d0c66e2923f510a501dc2a8f036601ecb01372c67df41ac6d4dc917e0379b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/office/calc_session_host_isolation_spec.spl
mirror: doc/06_spec/01_unit/app/office/calc_session_host_isolation_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/office/calc_session_host_isolation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/calc_session_host_isolation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/calc_session_host_isolation_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/office/calc_session_host_isolation_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the normal terminal owner free of access and capture transports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/calc_session_host_isolation_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'confines loopback transport to the explicit access adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
