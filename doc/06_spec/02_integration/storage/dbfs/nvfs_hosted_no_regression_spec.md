# nvfs_hosted_no_regression_spec

> NVFS Hosted Seam Specification

<!-- sdn-diagram:id=nvfs_hosted_no_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_hosted_no_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_hosted_no_regression_spec -> std
nvfs_hosted_no_regression_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_hosted_no_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_hosted_no_regression_spec

NVFS Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/nvfs_hosted_no_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

NVFS Hosted Seam Specification

Runs the same hosted mount-table contract as FAT32 so NVFS can share the
filesystem regression seam used by FAT32 and DBFS.

## Scenarios

### NVFS hosted seam — mount and stat

#### NVFS volume mounts without error

1. assert mount root is dir


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_nvfs_mounted()
assert_mount_root_is_dir(mt, "/nvfs")
```

</details>

#### stat on NVFS root returns is_dir=true

1. assert mount root slash is dir


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_nvfs_mounted()
assert_mount_root_slash_is_dir(mt, "/nvfs")
```

</details>

### NVFS hosted seam — readdir and open

#### readdir on NVFS root returns a stable empty-or-better listing

1. assert readdir on root is stable


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_nvfs_mounted()
assert_readdir_on_root_is_stable(mt, "/nvfs")
```

</details>

#### open on an NVFS path returns a valid handle

1. assert open returns handle


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_nvfs_mounted()
assert_open_returns_handle(mt, "/nvfs/README.TXT")
```

</details>

#### read on NVFS returns empty content rather than erroring

1. assert read returns empty or better


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_nvfs_mounted()
assert_read_returns_empty_or_better(mt, "/nvfs/README.TXT")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
