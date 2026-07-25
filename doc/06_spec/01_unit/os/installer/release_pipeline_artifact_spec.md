# Release Pipeline Artifact Specification

> 1.  reset dir

<!-- sdn-diagram:id=release_pipeline_artifact_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=release_pipeline_artifact_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

release_pipeline_artifact_spec -> std
release_pipeline_artifact_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=release_pipeline_artifact_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Release Pipeline Artifact Specification

## Scenarios

### Release pipeline artifacts

#### emits disk, iso, and release manifest files

1.  reset dir
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists("{dir}/x86_64/release.sdn") is true
   - Expected: rt_file_exists("{dir}/x86_64/images/simpleos-1.0.0-x86_64.img") is true
   - Expected: rt_file_exists("{dir}/x86_64/images/simpleos-1.0.0-x86_64-installer.iso") is true
   - Expected: rt_file_exists("{dir}/x86_64/images/simpleos-1.0.0-x86_64.img.manifest.sdn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "build/test-artifacts/release-pipeline"
_reset_dir(dir)
val config = ReleaseConfig(
    arch: PkgArch.X86_64,
    output_dir: dir,
    kernel_path: "",
    image_size_mb: 64
)
val result = release_all(config)
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists("{dir}/x86_64/release.sdn")).to_equal(true)
expect(rt_file_exists("{dir}/x86_64/images/simpleos-1.0.0-x86_64.img")).to_equal(true)
expect(rt_file_exists("{dir}/x86_64/images/simpleos-1.0.0-x86_64-installer.iso")).to_equal(true)
expect(rt_file_exists("{dir}/x86_64/images/simpleos-1.0.0-x86_64.img.manifest.sdn")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/release_pipeline_artifact_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Release pipeline artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
