# native_scalar_metadata_copy_spec

> REQ-BST-META-001: staged-native metadata copy keeps aggregates owner-local.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_scalar_metadata_copy_spec

REQ-BST-META-001: staged-native metadata copy keeps aggregates owner-local.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_scalar_metadata_copy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-BST-META-001: staged-native metadata copy keeps aggregates owner-local.

## Scenarios

### REQ-BST-META-001: scalar metadata transport

#### should append metadata without an aggregate ABI argument

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-BST-META-001
```

</details>

#### should update aligned metadata and ignore missing sources

- should update aligned metadata and ignore missing sources
- Update existing metadata and fail closed on an unknown source ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should update aligned metadata and ignore missing sources")
step("Update existing metadata and fail closed on an unknown source ID")
expect(_metadata_gate.0).to_contain("update=pass missing-source=pass")
```

</details>

#### should require a native pure-Simple candidate

- should require a native pure-Simple candidate
- Reject seed, compile failure, missing executable, and wrong output
   - Expected: _metadata_gate.1 equals ``
   - Expected: _metadata_gate.0 does not contain `STATUS: FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require a native pure-Simple candidate")
step("Reject seed, compile failure, missing executable, and wrong output")
expect(_metadata_gate.1).to_equal("")
expect(_metadata_gate.0.contains("STATUS: FAIL")).to_equal(false)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-BST-META-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73dbfa50551c26f5af380f5279d95d12eb0efc6887efff0251ddf2116950d553`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73dbfa50551c26f5af380f5279d95d12eb0efc6887efff0251ddf2116950d553`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73dbfa50551c26f5af380f5279d95d12eb0efc6887efff0251ddf2116950d553`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/compiler/native_scalar_metadata_copy_spec.spl
mirror: doc/06_spec/03_system/compiler/native_scalar_metadata_copy_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_scalar_metadata_copy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_scalar_metadata_copy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_scalar_metadata_copy_spec.spl:18:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should append metadata without an aggregate ABI argument' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/compiler/native_scalar_metadata_copy_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should append metadata without an aggregate ABI argument' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_scalar_metadata_copy_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should update aligned metadata and ignore missing sources' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_scalar_metadata_copy_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should update aligned metadata and ignore missing sources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_scalar_metadata_copy_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require a native pure-Simple candidate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/native_scalar_metadata_copy_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require a native pure-Simple candidate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
