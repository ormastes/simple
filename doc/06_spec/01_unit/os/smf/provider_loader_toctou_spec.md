# Provider Loader Toctou Specification

> Tests covering provider_admit_dynamic_v1 path digest is not bound to the loaded image.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Loader Toctou Specification

## Scenarios

### provider_admit_dynamic_v1 path digest is not bound to the loaded image

#### reads the loader source used by this repository

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the loader source used by this repository


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the loader source used by this repository")
val src = loader_source()
expect(src.len() > 0).to_be(true)
expect(src.contains("fn provider_admit_dynamic_v1")).to_be(true)
```

</details>

#### documents the defect: the digest is computed before the path is re-opened

- documents the defect: the digest is computed before the path is re-opened


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the defect: the digest is computed before the path is re-opened")
val body = fn_body(loader_source(), "provider_admit_dynamic_v1")
expect(body.len() > 0).to_be(true)
val before_open = body.split("dynlib_open(")[0]
expect(before_open.contains("provider_artifact_digest_v1(")).to_be(true)
```

</details>

#### requires a verify-after-open re-read of the artifact bytes

- requires a verify-after-open re-read of the artifact bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a verify-after-open re-read of the artifact bytes")
val body = fn_body(loader_source(), "provider_admit_dynamic_v1")
val after_open = segment_after(body, "dynlib_open(")
expect(after_open.len() > 0).to_be(true)
expect(after_open.contains("provider_artifact_digest_v1(")).to_be(true)
```

</details>

#### fails admission closed when the post-open re-read disagrees

- fails admission closed when the post-open re-read disagrees


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails admission closed when the post-open re-read disagrees")
val body = fn_body(loader_source(), "provider_admit_dynamic_v1")
val after_open = segment_after(body, "dynlib_open(")
expect(after_open.contains("PROVIDER_ADMISSION_DIGEST_UNSTABLE")).to_be(true)
expect(after_open.contains("dynlib_close(")).to_be(true)
```

</details>

#### swapping the artifact bytes changes the digest the loader would record

- swapping the artifact bytes changes the digest the loader would record


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("swapping the artifact bytes changes the digest the loader would record")
val path = "build/providers/toctou_probe_fixture.so"
val wrote_a = rt_file_atomic_write(path, "PROVIDER-IMAGE-A")
expect(wrote_a).to_be(true)
val a = rt_file_read_text(path) ?? ""
val wrote_b = rt_file_atomic_write(path, "PROVIDER-IMAGE-B-DIFFERENT")
expect(wrote_b).to_be(true)
val b = rt_file_read_text(path) ?? ""
expect(a == b).to_be(false)
rt_file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/smf/provider_loader_toctou_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering provider_admit_dynamic_v1 path digest is not bound to the loaded image.
- provider_admit_dynamic_v1 path digest is not bound to the loaded image

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96cc8a5db990fd2b956f777778761dcbf4718b913f303e20dc7e78f1af0fa216`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96cc8a5db990fd2b956f777778761dcbf4718b913f303e20dc7e78f1af0fa216`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96cc8a5db990fd2b956f777778761dcbf4718b913f303e20dc7e78f1af0fa216`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/smf/provider_loader_toctou_spec.spl
mirror: doc/06_spec/01_unit/os/smf/provider_loader_toctou_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smf/provider_loader_toctou_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smf/provider_loader_toctou_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/smf/provider_loader_toctou_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the loader source used by this repository' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smf/provider_loader_toctou_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the defect: the digest is computed before the path is re-opened' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smf/provider_loader_toctou_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a verify-after-open re-read of the artifact bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
