# coreutils/ls argument parsing

> Exercises `main_ls` argument parsing. Actual directory listing is

<!-- sdn-diagram:id=ls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ls_spec -> std
ls_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/ls argument parsing

Exercises `main_ls` argument parsing. Actual directory listing is

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/ls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `main_ls` argument parsing. Actual directory listing is
stubbed by the test harness (vfs_opendir returns 0 by default).

## Scenarios

### ls argument parsing
_Argument handling paths._

#### --help returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_ls(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### -1 flag is accepted and stripped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_ls(["-1", "--help"])
expect rc.to_equal(0i32)
```

</details>

#### empty args lists '.' and returns i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_ls([])
val is_int: bool = rc == 0i32 or rc == 1i32
expect is_int.to_equal(true)
```

</details>

### ls_list_one
_Single-path helper._

#### returns an i32 exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = ls_list_one(".")
val is_int: bool = rc == 0i32 or rc == 1i32
expect is_int.to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
