# Verified Release Delivery Gate Specification

> Tests covering FV2 verified-release delivery gate collector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verified Release Delivery Gate Specification

## Scenarios

### FV2 verified-release delivery gate collector

#### does not finalize caller-built release material as a passed gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not finalize caller-built release material as a passed gate
   - Expected: collection.gate_evidence.status.name() equals `failed`
   - Expected: collection.gate_evidence.receipt_hashes.len() equals `0`
   - Expected: collection.receipt_files.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not finalize caller-built release material as a passed gate")
val collection = collect_verified_release_gate_v1(
    pre_manifest_release_evidence(), [release_materials()[1]],
    [release_materials()[0], release_materials()[2],
        release_materials()[3], release_materials()[4],
        release_materials()[5]])
expect(collection.gate_evidence.status.name()).to_equal("failed")
expect(collection.gate_evidence.diagnostic).to_contain(
    "GATE-FINALIZER-AUTHORITY")
expect(collection.gate_evidence.receipt_hashes.len()).to_equal(0)
expect(collection.receipt_files.len()).to_equal(0)
```

</details>

#### rejects premature manifest sealing missing material and type confusion

- rejects premature manifest sealing missing material and type confusion


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects premature manifest sealing missing material and type confusion")
var sealed = pre_manifest_release_evidence()
sealed.delivery_gate_manifest_hash = sha256_text("already-sealed")
expect(collect_verified_release_gate_v1(sealed,
    [], release_materials()).gate_evidence.diagnostic).to_contain(
        "PREMANIFEST")
var missing = release_materials()
missing.pop()
expect(collect_verified_release_gate_v1(pre_manifest_release_evidence(),
    [], missing).gate_evidence.diagnostic).to_contain("MATERIAL-COUNT")
var confused = pre_manifest_release_evidence()
confused.mutation_receipt_hash = confused.trust_manifest_hash
expect(collect_verified_release_gate_v1(confused,
    [], release_materials()).gate_evidence.diagnostic).to_contain(
        "TYPE-CONFUSION")
```

</details>

#### rejects timeout stale and non-artifact-verified release claims

- rejects timeout stale and non-artifact-verified release claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects timeout stale and non-artifact-verified release claims")
var timeout = pre_manifest_release_evidence()
timeout.tool_outcomes = [ReleaseEvidenceOutcomeV1.Timeout]
expect(collect_verified_release_gate_v1(timeout,
    [], release_materials()).gate_evidence.status.name()).to_equal("failed")
var stale = pre_manifest_release_evidence()
stale.stale_evidence_count = 1
expect(collect_verified_release_gate_v1(stale,
    [], release_materials()).gate_evidence.status.name()).to_equal("failed")
var model_only = pre_manifest_release_evidence()
model_only.artifact_status = FormalStatus.ModelProven
expect(collect_verified_release_gate_v1(model_only,
    [], release_materials()).gate_evidence.status.name()).to_equal("failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/verified_release_delivery_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 verified-release delivery gate collector.
- FV2 verified-release delivery gate collector

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `13a5174da9ac60a55e2a360b6bedcca0f64e92b60fbd0c51dacc4856c86c9560`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13a5174da9ac60a55e2a360b6bedcca0f64e92b60fbd0c51dacc4856c86c9560`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13a5174da9ac60a55e2a360b6bedcca0f64e92b60fbd0c51dacc4856c86c9560`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/compiler/verification/verified_release_delivery_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/verified_release_delivery_gate_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/verified_release_delivery_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/verified_release_delivery_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/verified_release_delivery_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
