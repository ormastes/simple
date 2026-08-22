# CUDA Generated Font Handoff

> Verifies the cuda generated font handoff behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA Generated Font Handoff

Verifies the cuda generated font handoff behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the cuda generated font handoff behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### CUDA generated font handoff evidence

#### should reject PTX whose pinned provenance differs from canonical CUDA source

- Verify: should reject PTX whose pinned provenance differs from canonical CUDA source
- Compare the retained artifact provenance with the canonical CUDA emitter
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256 equals `sha256_text(ptx)`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION equals `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010 REQ-014
step("Verify: should reject PTX whose pinned provenance differs from canonical CUDA source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Compare the retained artifact provenance with the canonical CUDA emitter")
val ptx = cuda_font_atlas_composite_ptx()
val current = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.Cuda)
val current_source_sha256 = portable_compute_artifact_source_hash(current)
val current_version_sha256 = portable_compute_artifact_version_hash(current)
val source_matches = FONT_ATLAS_COMPOSITE_CUDA_SOURCE_SHA256 == current_source_sha256
val version_matches = FONT_ATLAS_COMPOSITE_CUDA_VERSION_SHA256 == current_version_sha256
expect(cuda_font_atlas_composite_provenance_trusted(current_source_sha256, current_version_sha256)).to_be(true)
expect(cuda_font_atlas_composite_provenance_trusted("tampered", current_version_sha256)).to_be(false)
expect(cuda_font_atlas_composite_provenance_trusted(current_source_sha256, "tampered")).to_be(false)
expect(source_matches).to_be(false)
expect(version_matches).to_be(false)
expect(source_matches and version_matches).to_be(false)
expect(FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256).to_equal(sha256_text(ptx))
expect(FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION).to_equal(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION)
expect(FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(cuda_font_atlas_composite_ptx_trusted(ptx)).to_be(false)
expect(cuda_font_atlas_composite_ptx_trusted(ptx + " ")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba1f22b00ba61fdc84318fafeaaca6727c38e6f48aeae0fb53204653df090226`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba1f22b00ba61fdc84318fafeaaca6727c38e6f48aeae0fb53204653df090226`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba1f22b00ba61fdc84318fafeaaca6727c38e6f48aeae0fb53204653df090226`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject PTX whose pinned provenance differs from canonical CUDA source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
