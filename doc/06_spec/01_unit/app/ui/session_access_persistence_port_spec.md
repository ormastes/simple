# Session Access Persistence Port Specification

> Tests covering UISession access persistence port.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Access Persistence Port Specification

## Scenarios

### UISession access persistence port

#### seeds and updates an attached storage-independent persistence port

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- seeds and updates an attached storage-independent persistence port
   - Expected: probe.snapshot_count equals `1`
   - Expected: probe.event_count equals `1`
   - Expected: probe.snapshot_count equals `2`
   - Expected: session.access_persisted_events("main", 10)?.len() equals `0`
   - Expected: session.access_search_nodes("main", "button", "save", 10)?.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("seeds and updates an attached storage-independent persistence port")
var probe = AccessPersistenceProbe(snapshot_count: 0, event_count: 0)
var session = UISession.new(build_tree(button("save", "Save", "save")))
session.attach_access_persistence(access_persistence_probe_port(probe))
expect(probe.snapshot_count).to_equal(1)

session.dispatch(UIEvent.Action(name: "save"))
expect(probe.event_count).to_equal(1)
expect(probe.snapshot_count).to_equal(2)
expect(session.access_persisted_events("main", 10)?.len()).to_equal(0)
expect(session.access_search_nodes("main", "button", "save", 10)?.len()).to_equal(0)
```

</details>

#### keeps persistence optional for the core session

- keeps persistence optional for the core session
   - Expected: session.access_persisted_events("main", 10).err().unwrap() equals `no access store attached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps persistence optional for the core session")
val session = UISession.new(build_tree(button("save", "Save", "save")))
expect(session.access_persisted_events("main", 10).err().unwrap()).to_equal("no access store attached")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/session_access_persistence_port_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UISession access persistence port.
- UISession access persistence port

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

- Canonical SPipe generation for source `c9d7336ab9ca358fd394c20be3854c74fc710469a64a24c75af016a3c545b59e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9d7336ab9ca358fd394c20be3854c74fc710469a64a24c75af016a3c545b59e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9d7336ab9ca358fd394c20be3854c74fc710469a64a24c75af016a3c545b59e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/ui/session_access_persistence_port_spec.spl
mirror: doc/06_spec/01_unit/app/ui/session_access_persistence_port_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/session_access_persistence_port_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/session_access_persistence_port_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/session_access_persistence_port_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/session_access_persistence_port_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seeds and updates an attached storage-independent persistence port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/session_access_persistence_port_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps persistence optional for the core session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
