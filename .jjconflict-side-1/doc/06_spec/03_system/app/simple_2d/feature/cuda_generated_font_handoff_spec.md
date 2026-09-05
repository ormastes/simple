# CUDA Generated Font Handoff

> Fail-closed evidence for the source-tracked CUDA font artifact while its

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA Generated Font Handoff

Fail-closed evidence for the source-tracked CUDA font artifact while its

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Fail-closed evidence for the source-tracked CUDA font artifact while its
straight-ARGB semantics lag the current common compositor. Canonical
regeneration with an admitted pure-Simple emitter is required before native
CUDA device-readback promotion can run again.

## Scenarios

### CUDA generated font handoff evidence

#### should reject the stale tracked artifact until canonical regeneration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject PTX whose pinned provenance differs from canonical CUDA source
- Compare the retained artifact provenance with the canonical CUDA emitter
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256 equals `sha256_text(ptx)`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION equals `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION equals `1`
   - Expected: FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject PTX whose pinned provenance differs from canonical CUDA source")
step("Compare the retained artifact provenance with the canonical CUDA emitter")
val ptx = cuda_font_atlas_composite_ptx()
val current = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.Cuda)
expect(FONT_ATLAS_COMPOSITE_CUDA_SOURCE_SHA256 == portable_compute_artifact_source_hash(current)).to_be(false)
expect(FONT_ATLAS_COMPOSITE_CUDA_VERSION_SHA256 == portable_compute_artifact_version_hash(current)).to_be(false)
expect(FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256).to_equal(sha256_text(ptx))
expect(FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION).to_equal(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION)
expect(FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION).to_equal(1)
expect(FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION).to_equal(2)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-010`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec424a7ac674061f2c97a373aec3c9b52e10f70314fb31873c2b0970e371c87a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec424a7ac674061f2c97a373aec3c9b52e10f70314fb31873c2b0970e371c87a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec424a7ac674061f2c97a373aec3c9b52e10f70314fb31873c2b0970e371c87a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=80
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject PTX whose pinned provenance differs from canonical CUDA source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject PTX whose pinned provenance differs from canonical CUDA source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
