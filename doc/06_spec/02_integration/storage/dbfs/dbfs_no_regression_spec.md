# dbfs_no_regression_spec

> DBFS Hosted Seam Specification

<!-- sdn-diagram:id=dbfs_no_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_no_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_no_regression_spec -> std
dbfs_no_regression_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_no_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_no_regression_spec

DBFS Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Hosted Seam Specification

Runs the same hosted mount-table contract as FAT32 so DBFS stays compatible
with shared filesystem regression coverage.

## Scenarios

### DBFS hosted seam — mount and stat

#### DBFS volume mounts without error

1. assert mount root is dir


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_mount_root_is_dir(mt, "/data")
```

</details>

#### stat on DBFS root returns is_dir=true

1. assert mount root slash is dir


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_mount_root_slash_is_dir(mt, "/data")
```

</details>

### DBFS hosted seam — readdir and open

#### readdir on DBFS root returns a stable empty-or-better listing

1. assert readdir on root is stable


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_readdir_on_root_is_stable(mt, "/data")
```

</details>

#### open on a DBFS path returns a valid handle

1. assert open returns handle


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_open_returns_handle(mt, "/data/README.TXT")
```

</details>

#### read on DBFS returns empty content rather than erroring

1. assert read returns empty or better


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = make_dbfs_mounted()
assert_read_returns_empty_or_better(mt, "/data/README.TXT")
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
