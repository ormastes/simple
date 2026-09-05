# Provider Durable Identity Specification

> Tests covering SPipe durable identity closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Durable Identity Specification

## Scenarios

### SPipe durable identity closure

#### accepts exact IdText and lowercase HashText persisted identities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts exact IdText and lowercase HashText persisted identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts exact IdText and lowercase HashText persisted identities")
expect(restore_identity("DOC-IDENTITY", "REV-IDENTITY",
    "sha256:" + "2" * 64, true)).to_be(true)
```

</details>

#### rejects control IDs uppercase visibility hashes and noncanonical preimages

- rejects control IDs uppercase visibility hashes and noncanonical preimages


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects control IDs uppercase visibility hashes and noncanonical preimages")
expect(restore_identity("DOC-\u0001", "REV-IDENTITY",
    "sha256:" + "2" * 64, true)).to_be(false)
expect(restore_identity("DOC-IDENTITY", "REV-\u0085",
    "sha256:" + "2" * 64, true)).to_be(false)
expect(restore_identity("DOC-IDENTITY", "REV-IDENTITY",
    "sha256:" + "A" * 64, true)).to_be(false)
expect(restore_identity("DOC-IDENTITY", "REV-IDENTITY",
    "sha256:" + "2" * 64, false)).to_be(false)
```

</details>

#### keeps SnapshotId distinct from HashText at the host boundary

- keeps SnapshotId distinct from HashText at the host boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps SnapshotId distinct from HashText at the host boundary")
expect(ProviderHostBindingV1.create("WS-PROVIDER", identity_snapshot(),
    identity_scope()).is_ok()).to_be(true)
expect(ProviderHostBindingV1.create("WS-PROVIDER",
    "sha256:" + "0" * 64, identity_scope()).is_err()).to_be(true)
expect(ProviderHostBindingV1.create("WS-PROVIDER",
    "spks1-" + "A" * 64, identity_scope()).is_err()).to_be(true)
expect(ProviderHostBindingV1.create("provider",
    identity_snapshot(), identity_scope()).is_err()).to_be(true)
```

</details>

#### requires exact canonical outer lifecycle bytes

- requires exact canonical outer lifecycle bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires exact canonical outer lifecycle bytes")
val canonical = "{\"candidates\":[],\"current_logical_root\":\"sha256:" +
    "3" * 64 + "\",\"provider_generation\":1,\"publications\":[]," +
    "\"replay\":[],\"schema\":\"spipe-provider-lifecycle-store-v1\"," +
    "\"scope_digest\":\"" + identity_scope() + "\",\"snapshot\":\"" +
    identity_snapshot() + "\",\"workspace\":\"WS-PROVIDER\"}"
expect(lifecycle_json_bytes_canonical(canonical)).to_be(true)
expect(lifecycle_json_bytes_canonical(" " + canonical)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe durable identity closure.
- SPipe durable identity closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd05aac0bb29cbe48ee2ef29d753613ecca05fc31fd744c463c9f920d5f7265c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd05aac0bb29cbe48ee2ef29d753613ecca05fc31fd744c463c9f920d5f7265c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd05aac0bb29cbe48ee2ef29d753613ecca05fc31fd744c463c9f920d5f7265c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts exact IdText and lowercase HashText persisted identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects control IDs uppercase visibility hashes and noncanonical preimages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_durable_identity_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps SnapshotId distinct from HashText at the host boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
