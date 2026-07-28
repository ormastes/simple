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
| Updated | 2026-07-25 |
| Generator | manually synchronized; executable docgen refresh pending |

Fail-closed evidence for the source-tracked CUDA font artifact while its
straight-ARGB semantics lag the current common compositor. Canonical
regeneration with an admitted pure-Simple emitter is required before native
CUDA device-readback promotion can run again.

## Scenarios

### CUDA generated font handoff evidence

#### should reject PTX whose pinned provenance differs from canonical CUDA source

- Compare the retained artifact provenance with the canonical CUDA emitter
   - Expected: canonical source and version digests pass independently
   - Expected: either tampered digest fails independently
   - Expected: retained source and version digests remain stale
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256 equals `sha256_text(ptx)`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION equals `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION equals `1`
   - Expected: FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
