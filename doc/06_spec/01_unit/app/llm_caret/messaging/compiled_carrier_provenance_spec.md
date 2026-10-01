# Compiled Carrier Provenance Specification

> Tests covering LLM Caret compiled carrier provenance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiled Carrier Provenance Specification

## Scenarios

### LLM Caret compiled carrier provenance

#### rejects artifacts without exact source dependency and compiler provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects artifacts without exact source dependency and compiler provenance
- Create an isolated carrier fixture without invoking the compiler
   - Expected: messaging_artifact_fresh(plan, [dependency]) is false
- Record the exact compiler source and dependency identity
   - Expected: messaging_artifact_fresh(plan, [dependency]) is true
- Reject a forged or stale provenance record
   - Expected: messaging_artifact_fresh(plan, [dependency]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects artifacts without exact source dependency and compiler provenance")
step("Create an isolated carrier fixture without invoking the compiler")
val root = "build/verify/llm-caret-messaging-provenance"
mkdir_p(root)
val source = root + "/worker.spl"
val dependency = root + "/database.spl"
val artifact = root + "/worker.bin"
file_write(source, "fn main() -> i64: 0\n")
file_write(dependency, "fn database_marker() -> text: \"pure-simple\"\n")
file_write(artifact, "fixture-only")
val plan = DatabaseExecutionPlan(kind: DatabaseArtifactKind.NativeExecutable,
    artifact_path: artifact, source_path: source,
    requires_fresh_artifact: true, reason: "test")
expect(messaging_artifact_fresh(plan, [dependency])).to_equal(false)

step("Record the exact compiler source and dependency identity")
val provenance = messaging_artifact_provenance(plan, [dependency], "bin/simple")
file_write(artifact + ".provenance.sdn", provenance)
expect(messaging_artifact_fresh(plan, [dependency])).to_equal(true)

step("Reject a forged or stale provenance record")
file_write(artifact + ".provenance.sdn", provenance + "unexpected=true\n")
expect(messaging_artifact_fresh(plan, [dependency])).to_equal(false)
file_delete(artifact + ".provenance.sdn")
file_delete(artifact)
file_delete(dependency)
file_delete(source)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret compiled carrier provenance.
- LLM Caret compiled carrier provenance

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

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-013`
- `REQ-LLM-MSG-016`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `52343620a26d02290f7584269f54c9b6ab5203d9c89056950288651f97296a5c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52343620a26d02290f7584269f54c9b6ab5203d9c89056950288651f97296a5c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52343620a26d02290f7584269f54c9b6ab5203d9c89056950288651f97296a5c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects artifacts without exact source dependency and compiler provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
