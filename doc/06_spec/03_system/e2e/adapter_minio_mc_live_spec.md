# Adapter Minio Mc Live Specification

> Tests covering adapter_minio_mc — live local MinIO.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Minio Mc Live Specification

## Scenarios

### adapter_minio_mc — live local MinIO

#### health endpoint returns ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
```

</details>

#### ls --recursive returns the seeded objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = McClient(alias_name: "localtest", mc_path: "mc")
val (ok, entries, _raw) = mc_ls(client, "spipe-test-bucket", true)
expect(ok).to_be(true)
expect(entries.len() >= 3).to_be(true)
```

</details>

#### stat returns metadata for firmware/v1.2.3.bin

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = McClient(alias_name: "localtest", mc_path: "mc")
val (ok, _info, _raw) = mc_stat(client, "spipe-test-bucket/firmware/v1.2.3.bin")
expect(ok).to_be(true)
```

</details>

#### get fetches notes file to local path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = McClient(alias_name: "localtest", mc_path: "mc")
val (ok, _entries, _raw) = mc_get(client, "spipe-test-bucket/notes/simple-42.md", "/tmp/notes_fetched.md")
expect(ok).to_be(true)
```

</details>

#### share download produces a presigned URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = McClient(alias_name: "localtest", mc_path: "mc")
val (ok, presigned, _raw) = mc_share_download(client, "spipe-test-bucket/dumps/simple-42.dmp", 3600)
expect(ok).to_be(true)
expect(presigned.len() > 0).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/e2e/adapter_minio_mc_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering adapter_minio_mc — live local MinIO.
- adapter_minio_mc — live local MinIO

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4d5ea9d4a94f57f1476a764988f122bbdea01bfea500a5bc5af36b2e52a8fbba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d5ea9d4a94f57f1476a764988f122bbdea01bfea500a5bc5af36b2e52a8fbba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d5ea9d4a94f57f1476a764988f122bbdea01bfea500a5bc5af36b2e52a8fbba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/e2e/adapter_minio_mc_live_spec.spl
mirror: doc/06_spec/03_system/e2e/adapter_minio_mc_live_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/e2e/adapter_minio_mc_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/e2e/adapter_minio_mc_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/e2e/adapter_minio_mc_live_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/03_system/e2e/adapter_minio_mc_live_spec.spl:11:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'health endpoint returns ready' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_minio_mc_live_spec.spl:18:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ls --recursive returns the seeded objects' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_minio_mc_live_spec.spl:25:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'stat returns metadata for firmware/v1.2.3.bin' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/e2e/adapter_minio_mc_live_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'get fetches notes file to local path' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
