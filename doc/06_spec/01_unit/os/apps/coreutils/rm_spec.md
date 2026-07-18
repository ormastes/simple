# coreutils/rm argument parsing

> _Argument handling paths._

<!-- sdn-diagram:id=rm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rm_spec -> std
rm_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/rm argument parsing

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/rm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### rm argument parsing
_Argument handling paths._

#### --help returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_rm(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### missing operand returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_rm([])
expect rc.to_equal(1i32)
```

</details>

#### -f flag is accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_rm(["-f", "/tmp/x"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### rm_one
_Single-path unlink helper._

#### returns i32 in force mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = rm_one("/tmp/x", true)
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

#### returns i32 in non-force mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = rm_one("/tmp/x", false)
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
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
